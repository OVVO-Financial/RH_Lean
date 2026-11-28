#!/usr/bin/env python3
"""Require a current, independent mathematical approval of the exact #1214 head."""
import json
import os
import re
import subprocess
import sys

REPOSITORY = "OVVO-Financial/RH_Lean"
PR = 1214
TRUSTED = {"OWNER", "MEMBER", "COLLABORATOR"}


def require_review(pr, reviews, sha):
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise ValueError("Missing exact proof commit")
    if (pr["number"] != PR or pr["state"] != "open" or pr["head"]["sha"] != sha
            or pr["base"]["repo"]["full_name"].lower() != REPOSITORY.lower()):
        raise ValueError("Review evidence does not belong to the current #1214 proof commit")
    author = pr["user"]["login"].lower()
    current = {}
    for review in sorted(reviews, key=lambda r: (r.get("submitted_at") or "", r["id"])):
        user = review.get("user") or {}
        login = user.get("login", "").lower()
        state = review["state"].upper()
        if (login and login != author and user.get("type") == "User"
                and not login.endswith("[bot]") and review.get("author_association") in TRUSTED
                and state in {"APPROVED", "CHANGES_REQUESTED", "DISMISSED"}):
            current[login] = review
    marker = f"I reviewed the native RH terminal supplier chain and all ten acceptance criteria at {sha}."
    approved = []
    for login, review in current.items():
        if review.get("commit_id") != sha:
            continue
        if review["state"].upper() == "CHANGES_REQUESTED":
            raise ValueError(f"Outstanding mathematical changes requested by {login}")
        if review["state"].upper() == "APPROVED" and marker in (review.get("body") or "").splitlines():
            approved.append(login)
    if not approved:
        raise ValueError(f"Independent human mathematical review of {sha} is pending")
    return sorted(approved)


def github(api_path, *, paginate=False):
    args = ["gh", "api"]
    if paginate:
        args.extend(["--paginate", "--slurp"])
    result = subprocess.run([*args, api_path], check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def main():
    sha = os.environ["PROOF_HEAD"]
    route = f"repos/{REPOSITORY}/pulls/{PR}"
    pages = github(route + "/reviews?per_page=100", paginate=True)
    reviewers = require_review(github(route), [r for page in pages for r in page], sha)
    print(f"Independently approved terminal mathematical chain at {sha} by {', '.join(reviewers)}")


if __name__ == "__main__":
    try:
        main()
    except (KeyError, TypeError, ValueError, subprocess.CalledProcessError) as exc:
        sys.exit(f"Terminal review gate failed: {exc}")
