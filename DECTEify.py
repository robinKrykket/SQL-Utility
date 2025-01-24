#Tool built to remove CTE's from queries so that they can be used by Microsoft SQL Server
#This code is built to take a SQL document with CTEs (common expressions) as an input and return a new SQL document with those CTEs inlined into the main query
#Set the CD to the folder that contains this file.
#Run command with the follwing syntax: python DECTEify.py "sql_file_path.sql" -o "output_directory_location"

import re
from collections import defaultdict, deque
from pathlib import Path
import argparse

# Initialize parser
parser = argparse.ArgumentParser(description="A sample argparse program.")

# Add arguments
parser.add_argument("file_path", type=str, help="Location of the file you would like to convert")
parser.add_argument("-o", "--output", type=str, help="Path to the output direcotry")

# Parse arguments
args = parser.parse_args()


def split_with_and_select(sql_text):
    """
    Splits the SQL text into (with_block, main_select).
    1) Locates the first top-level SELECT after a WITH.
    2) If no WITH found, returns ("", sql_text).
    """
    # Basic normalization of whitespace
    sql_text = re.sub(r'[ \t]+', ' ', sql_text)

    with_match = re.search(r'\bWITH\b', sql_text, flags=re.IGNORECASE)
    if not with_match:
        return "", sql_text.strip()

    start_idx = with_match.start()
    paren_count = 0
    main_select_start = -1
    i = start_idx
    n = len(sql_text)
    sql_upper = sql_text.upper()

    while i < n:
        ch = sql_text[i]
        if ch == '(':
            paren_count += 1
        elif ch == ')':
            paren_count -= 1

        # Look for top-level SELECT
        if paren_count == 0 and sql_upper[i : i + 6] == "SELECT":
            main_select_start = i
            break
        i += 1

    if main_select_start == -1:
        # Found WITH but never found a top-level SELECT
        return sql_text[start_idx:].strip(), ""

    with_block = sql_text[start_idx:main_select_start].strip()
    main_select = sql_text[main_select_start:].strip()
    return with_block, main_select


def extract_ctes(sql_text):
    """
    Parses out CTEs from the WITH block and returns:
        ctes       : dict { cte_name.lower(): cte_body }
        main_select: everything after the WITH block
    If there's no WITH, returns empty dict and the original text.
    """
    with_block, main_select = split_with_and_select(sql_text)
    if not with_block:
        return {}, sql_text.strip()

    # Remove leading/trailing "WITH"
    with_block = re.sub(r'^\s*WITH\s+', '', with_block, flags=re.IGNORECASE).strip()

    # Split the with_block by top-level commas
    ctes_text_list = []
    paren_count = 0
    start_idx = 0
    for i, char in enumerate(with_block):
        if char == '(':
            paren_count += 1
        elif char == ')':
            paren_count -= 1

        # If paren_count == 0 and we see a comma, that's a boundary
        if paren_count == 0 and char == ',':
            ctes_text_list.append(with_block[start_idx:i].strip().rstrip(','))
            start_idx = i + 1
    final_chunk = with_block[start_idx:].strip().rstrip(',')
    if final_chunk:
        ctes_text_list.append(final_chunk)

    # Parse each chunk "CTENAME AS ( ... )"
    cte_pattern = re.compile(r'^([\w\d_]+)\s+AS\s*\((.*)\)$', re.IGNORECASE | re.DOTALL)
    ctes = {}
    for chunk in ctes_text_list:
        m = cte_pattern.match(chunk)
        if not m:
            continue
        cte_name = m.group(1).strip()
        cte_body = m.group(2).strip()
        ctes[cte_name.lower()] = cte_body

    return ctes, main_select


def find_dependencies(ctes):
    """
    For each cte_name -> cte_body, see which other ctes appear in its body.
    Returns a dict { cte_name: set(of dependencies) }
    """
    dep_map = defaultdict(set)
    cte_names = list(ctes.keys())

    for cte, body in ctes.items():
        body_upper = body.upper()
        for other_cte in cte_names:
            if other_cte == cte:
                continue
            pattern = r'\b' + re.escape(other_cte.upper()) + r'\b'
            if re.search(pattern, body_upper):
                dep_map[cte].add(other_cte)
    return dep_map


def topological_sort_ctes(dep_map):
    """
    Returns a list of ctes in an order such that dependencies come first.
    """
    in_degree = defaultdict(int)
    all_ctes = set(dep_map.keys())

    # Include ctes that appear only as dependencies
    for deps in dep_map.values():
        all_ctes.update(deps)

    for cte, deps in dep_map.items():
        for d in deps:
            in_degree[cte] += 1

    queue = deque(cte for cte in all_ctes if in_degree[cte] == 0)
    sorted_list = []

    while queue:
        node = queue.popleft()
        sorted_list.append(node)
        for cte, deps in dep_map.items():
            if node in deps:
                in_degree[cte] -= 1
                if in_degree[cte] == 0:
                    queue.append(cte)

    return [s for s in sorted_list if s in all_ctes]


def inline_cte(target_sql, cte_name, cte_body):
    """
    Replace references to `cte_name` with '(( cte_body )) [AS user_alias_or_cte_name]'
    in FROM/JOIN clauses or subselect usage.

    This carefully preserves:
      - The user-defined alias if present (AS s, or s)
      - Any trailing text, e.g. 'ON ...'
      - Uses double parentheses '(( ... ))'
    """
    # We'll unify both FROM/JOIN usage and subselect usage into a single approach.
    # Idea: 
    #   1) Capture the leading "FROM ...", "JOIN ...", etc.
    #   2) Capture the cte_name
    #   3) Optionally capture "AS something" or "something" as an alias
    #   4) Capture everything after that alias (like "ON ..." or ") ...")

    # For example, from "LEFT JOIN starts as s on s.x = y",
    # group(1) = "LEFT JOIN "
    # group(2) = "starts"
    # group(4) = "as" or None
    # group(5) = "s" or None
    # group(6) = " on s.x = y"

    # We'll replace it with:
    #   "LEFT JOIN (( cte_body )) AS s on s.x = y"
    # if group(5) is present,
    # or "LEFT JOIN (( cte_body )) AS starts on s.x = y" if there's no user alias.

    # 1) Pattern for FROM/JOIN usage
    pattern_from_join = re.compile(
        rf'(\bFROM\s+|\bJOIN\s+|\bINNER\s+JOIN\s+|\bLEFT\s+JOIN\s+|\bRIGHT\s+JOIN\s+|\bFULL\s+JOIN\s+)'
        rf'({cte_name})'
        r'(?:\s+(AS\s+)?(\w+))?'
        r'(.*)',  # capture any trailing text
        flags=re.IGNORECASE | re.DOTALL
    )

    def replace_from_join(m):
        join_keyword = m.group(1)             # e.g. "LEFT JOIN "
        # m.group(2) is the actual cte_name, not needed again
        possible_as = m.group(3)             # "AS " or None
        user_alias = m.group(4)             # e.g. "s"
        the_rest = m.group(5) or ""         # e.g. " on s.x = y"

        if user_alias:
            alias_to_use = user_alias
        else:
            # If there's no user alias, just use the cte_name
            alias_to_use = cte_name

        # Double parentheses around cte_body, then "AS <alias>"
        return f"{join_keyword}((\n{cte_body}\n)) AS {alias_to_use}{the_rest}"

    new_sql = pattern_from_join.sub(replace_from_join, target_sql)

    # 2) Subselect usage. For example:
    #    "WHERE x IN (SELECT ... FROM starts AS s) ... "
    # We do a similar pattern to preserve user alias and trailing text.
    # We'll allow optional parentheses before the cte_name (like "FROM (starts" is rare but possible).
    pattern_subselect = re.compile(
        rf'(\bFROM\s+\(?)\s*({cte_name})(?:\s+(AS\s+)?(\w+))?(.*)',
        flags=re.IGNORECASE | re.DOTALL
    )

    def replace_subselect(m):
        before_from = m.group(1)            # e.g. "FROM " or "FROM ("
        # m.group(2) is cte_name
        possible_as = m.group(3)
        user_alias = m.group(4)
        the_rest = m.group(5) or ""

        if user_alias:
            alias_to_use = user_alias
        else:
            alias_to_use = cte_name

        return f"{before_from}((\n{cte_body}\n)) AS {alias_to_use}{the_rest}"

    new_sql = pattern_subselect.sub(replace_subselect, new_sql)

    return new_sql


def fix_division_by_zero(sql_text):
    """
    Replaces 'x / y' with 'x / NULLIF(y, 0)' (naive approach).
    This can cause oddities in more complex expressions, but
    is sufficient for many simpler queries.
    """
    pattern_div = re.compile(r'(\S+)\s*/\s*(\S+)')
    def repl_div(m):
        left = m.group(1)
        right = m.group(2)
        return f"{left} / NULLIF({right}, 0)"
    return pattern_div.sub(repl_div, sql_text)


def inline_all_ctes(sql_text):
    """
    1) Extract CTEs
    2) Determine dependencies
    3) Sort in dependency order
    4) Inline from the least dependent to the most dependent
    5) Replace divisions with x / NULLIF(y,0)
    6) Return the final SQL
    """
    ctes, main_select = extract_ctes(sql_text)
    if not ctes:
        # No CTEs, just do the final division fix
        return fix_division_by_zero(sql_text).strip()

    dep_map = find_dependencies(ctes)
    for cte in ctes:
        dep_map.setdefault(cte, set())

    sorted_ctes = topological_sort_ctes(dep_map)

    final_sql = main_select
    # Inline from least dependent to most dependent
    for cte in sorted_ctes:
        body = ctes[cte]
        # Inline into the main SELECT
        final_sql = inline_cte(final_sql, cte, body)

        # Also inline references within the other CTE definitions
        for other in sorted_ctes:
            if other != cte:
                ctes[other] = inline_cte(ctes[other], cte, body)

    # Now fix divisions
    final_sql = fix_division_by_zero(final_sql)
    return final_sql.strip()
if args.output:
    output_dir = Path(args.output)
def main():
    input_file = Path(args.file_path)
    if not input_file.exists():
        print(f"Error: File not found: {input_file}")
        return
    
    if args.output:
        output_file = output_dir / f"{input_file.stem}_decteified{input_file.suffix}"
    else:
        output_file = input_file.parent / f"{input_file.stem}_decteified{input_file.suffix}"
   
    original_sql = input_file.read_text(encoding='utf-8')

    inlined_sql = inline_all_ctes(original_sql)
    output_file.write_text(inlined_sql + "\n", encoding='utf-8')
    print(f"De-CTEified SQL saved to: {output_file}")


if __name__ == "__main__":
    main()
