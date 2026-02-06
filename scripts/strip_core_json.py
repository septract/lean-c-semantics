#!/usr/bin/env python3
"""
Strip a Cerberus Core JSON file to only include functions reachable from main.

Usage:
    ./scripts/strip_core_json.py input.json output.json
    ./scripts/strip_core_json.py input.json  # outputs to stdout
"""

import json
import sys
import os


def find_calls(obj, calls=None):
    """Recursively find all function/symbol references in an AST node."""
    if calls is None:
        calls = set()

    if isinstance(obj, dict):
        # Check for symbol references (e.g., {"tag": "Sym", "symbol": {"name": "foo"}})
        if obj.get('tag') == 'Sym' and 'symbol' in obj:
            sym = obj['symbol']
            if isinstance(sym, dict) and 'name' in sym:
                calls.add(sym['name'])
        # Check for direct name references
        if 'name' in obj and isinstance(obj['name'], str):
            calls.add(obj['name'])
        # Recurse into all values
        for v in obj.values():
            find_calls(v, calls)
    elif isinstance(obj, list):
        for item in obj:
            find_calls(item, calls)

    return calls


def compute_reachable(all_fns, roots):
    """Compute transitive closure of functions reachable from roots."""
    needed = set(roots)
    worklist = list(roots)

    while worklist:
        fn_name = worklist.pop()
        if fn_name not in all_fns:
            continue
        fn = all_fns[fn_name]
        calls = find_calls(fn)
        for call in calls:
            if call not in needed and call in all_fns:
                needed.add(call)
                worklist.append(call)

    return needed


def strip_locations(obj):
    """Recursively replace verbose location data with null."""
    if isinstance(obj, dict):
        result = {}
        for k, v in obj.items():
            if k == 'loc' and isinstance(v, dict) and v.get('tag') == 'Region':
                result[k] = None  # Strip verbose location
            elif k == 'cursor':
                result[k] = None  # Strip cursor info
            else:
                result[k] = strip_locations(v)
        return result
    elif isinstance(obj, list):
        return [strip_locations(item) for item in obj]
    else:
        return obj


def strip_json(data, verbose=False, strip_locs=False, strip_funinfo=False, strip_extern=False):
    """Strip JSON to only include functions reachable from main."""
    # Build function maps
    stdlib_map = {fn['symbol']['name']: fn for fn in data.get('stdlib', [])}
    funs_map = {fn['symbol']['name']: fn for fn in data.get('funs', [])}
    all_fns = {**stdlib_map, **funs_map}

    # Find main
    main_sym = data.get('main', {})
    main_name = main_sym.get('name', 'main') if isinstance(main_sym, dict) else 'main'

    if main_name not in all_fns:
        print(f"Warning: main function '{main_name}' not found", file=sys.stderr)
        return data

    # Compute reachable functions
    needed = compute_reachable(all_fns, [main_name])

    if verbose:
        print(f"Reachable functions ({len(needed)}):", file=sys.stderr)
        for name in sorted(needed):
            src = "stdlib" if name in stdlib_map else "funs"
            print(f"  {name} ({src})", file=sys.stderr)

    # Filter funinfo to only needed functions
    funinfo = data.get('funinfo', {})
    if strip_funinfo:
        if isinstance(funinfo, list):
            funinfo = [item for item in funinfo
                      if item.get('symbol', {}).get('name') in needed]
        elif isinstance(funinfo, dict):
            funinfo = {k: v for k, v in funinfo.items() if k in needed}

    # Create stripped JSON
    stripped = {
        'main': data['main'],
        'calling_convention': data['calling_convention'],
        'tagDefs': data.get('tagDefs', []),
        'stdlib': [fn for fn in data.get('stdlib', []) if fn['symbol']['name'] in needed],
        'impl': data.get('impl', []),
        'globs': data.get('globs', []),
        'funs': [fn for fn in data.get('funs', []) if fn['symbol']['name'] in needed],
        'extern': [] if strip_extern else data.get('extern', {}),
        'funinfo': funinfo,
        'loop_attributes': data['loop_attributes'],
        'visible_objects_env': data['visible_objects_env'],
    }

    # Optionally strip location data
    if strip_locs:
        stripped = strip_locations(stripped)

    return stripped


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', help='Input JSON file')
    parser.add_argument('output', nargs='?', help='Output JSON file (stdout if omitted)')
    parser.add_argument('-v', '--verbose', action='store_true', help='Show reachable functions')
    parser.add_argument('--strip-locs', action='store_true', help='Strip verbose location data')
    parser.add_argument('--strip-funinfo', action='store_true', help='Strip unused funinfo entries')
    parser.add_argument('--strip-extern', action='store_true', help='Strip extern mappings')
    parser.add_argument('--aggressive', action='store_true', help='Enable all stripping options')
    args = parser.parse_args()

    input_path = args.input
    output_path = args.output
    verbose = args.verbose
    strip_locs = args.strip_locs or args.aggressive
    strip_funinfo = args.strip_funinfo or args.aggressive
    strip_extern = args.strip_extern or args.aggressive

    # Load input
    with open(input_path) as f:
        data = json.load(f)

    orig_size = os.path.getsize(input_path)

    # Strip
    stripped = strip_json(data, verbose=verbose, strip_locs=strip_locs,
                          strip_funinfo=strip_funinfo, strip_extern=strip_extern)

    # Output
    output_json = json.dumps(stripped, indent=2)

    if output_path:
        with open(output_path, 'w') as f:
            f.write(output_json)
        new_size = os.path.getsize(output_path)
        print(f"Stripped {input_path} -> {output_path}", file=sys.stderr)
        print(f"  {orig_size:,} bytes -> {new_size:,} bytes ({100*new_size/orig_size:.1f}%)", file=sys.stderr)
    else:
        print(output_json)


if __name__ == '__main__':
    main()
