import copy
import unittest
from native_rh_review import require_review, REPOSITORY, PR


class TerminalReviewTest(unittest.TestCase):
    def setUp(self):
        self.sha = "a" * 40
        self.pr = {"number": PR, "state": "open", "head": {"sha": self.sha},
                   "base": {"repo": {"full_name": REPOSITORY}}, "user": {"login": "author"}}
        self.review = {"id": 1, "submitted_at": "2026-11-26T12:00:00Z", "state": "APPROVED",
                       "user": {"login": "reviewer", "type": "User"}, "author_association": "MEMBER",
                       "commit_id": self.sha,
                       "body": f"I reviewed the native RH terminal supplier chain and all ten acceptance criteria at {self.sha}."}

    def test_authenticated_approval_at_current_head(self):
        self.assertEqual(require_review(self.pr, [self.review], self.sha), ["reviewer"])

    def test_unreviewed_stale_and_untrusted_do_not_pass(self):
        for change in ({"commit_id": "b" * 40}, {"author_association": "NONE"},
                       {"state": "COMMENTED"}, {"body": "LGTM"},
                       {"user": {"login": "author", "type": "User"}},
                       {"user": {"login": "automation[bot]", "type": "Bot"}}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                require_review(self.pr, [{**self.review, **change}], self.sha)
        pr = copy.deepcopy(self.pr)
        pr["head"]["sha"] = "c" * 40
        with self.assertRaises(ValueError):
            require_review(pr, [self.review], self.sha)
        with self.assertRaises(ValueError):
            require_review(self.pr, [], self.sha)

    def test_dismissal_and_changes_requested_revoke(self):
        for state in ("DISMISSED", "CHANGES_REQUESTED"):
            review = {**self.review, "id": 2, "state": state}
            with self.subTest(state=state), self.assertRaises(ValueError):
                require_review(self.pr, [review, self.review], self.sha)
        other = {**self.review, "id": 3, "state": "CHANGES_REQUESTED",
                 "user": {"login": "second-reviewer", "type": "User"}}
        with self.assertRaises(ValueError):
            require_review(self.pr, [self.review, other], self.sha)
