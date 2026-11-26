#!/usr/bin/env python3
"""Independent direct checks. A good witness is not an optimality certificate."""
import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path


def valid(values):
    return all((b+c) % a for a,b,c in itertools.combinations(values, 3))


def score(values):
    return sum((Fraction(1,a) for a in values), Fraction())


def verify(record):
    witness = record["witness"]
    if record["schema"] != 1 or record["conjecture"] != "property-p-sharp":
        raise ValueError("unexpected schema or conjecture")
    if not witness or any(type(a) is not int for a in witness):
        raise ValueError("witness must contain positive, distinct integers")
    if witness != sorted(set(witness)) or not 1 <= record["min_element"] <= witness[0] <= witness[-1] <= record["n"]:
        raise ValueError("witness out of bounds or not strictly sorted")
    if not valid(witness):
        raise ValueError("forbidden triple in witness")
    value = score(witness)
    if value != Fraction(record["score"]) or record["exceeds_target"] is not (value > Fraction(3, 2)):
        raise ValueError("inconsistent exact score or threshold flag")
    return value


def brute_force(n, low=1):
    if not 1 <= low <= n <= 18:
        raise ValueError("independent brute-force check supports n <= 18")
    return max(score(a)
               for size in range(n-low+2)
               for a in itertools.combinations(range(low,n+1), size)
               if valid(a))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", nargs="+", type=Path)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--brute-force", action="store_true")
    group.add_argument("--replay", action="store_true", help="rerun the exact solver on each complete report")
    args = parser.parse_args()
    for path in args.report:
        rec = json.loads(path.read_text(encoding="utf-8"))
        value = verify(rec)
        if args.brute_force:
            if value != brute_force(rec["n"], rec["min_element"]):
                raise ValueError("witness is not the exact finite optimum")
            print(f"{path}: independently verified exact optimum {value}")
        elif args.replay:
            from lab import optimize
            if not 1 <= rec["min_element"] <= rec["n"] <= 500 or not 1 <= rec["budget"] <= 3_000_000:
                raise ValueError("replay exceeds the documented executable bounds")
            if rec["mode"] != "exact" or rec["complete"] is not True or rec["status"] != "finite_optimum":
                raise ValueError("replay requires a completed exact report")
            _, replay_value, replay_work, complete = optimize(rec["n"], rec["min_element"], rec["budget"])
            if not complete or (replay_value, replay_work) != (value, rec["work"]):
                raise ValueError("exact search did not reproduce the recorded result")
            print(f"{path}: exact optimum {value} reproduced in {replay_work} nodes; same algorithm")
        else:
            print(f"{path}: verified witness and exact score {value}; optimality not independently checked")


if __name__ == "__main__":
    main()
