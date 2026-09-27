import unittest

from run import Case, parse_results, summarize


class ResultProtocolTests(unittest.TestCase):
    def setUp(self):
        self.cases = (Case("refl_reuse", 0, 256),)

    def test_hol4_prompt_and_trial_summary(self):
        output = (
            "> HOTARU_BENCH\trefl_reuse\t0\t0\t256\t2560\n"
            "HOTARU_BENCH\trefl_reuse\t0\t1\t256\t5120\n"
        )
        results = parse_results(output, "hol4", self.cases, 2)
        summary = summarize(results, self.cases, ("hol4",))
        self.assertEqual(len(results), 2)
        self.assertEqual(summary[0]["median_ns_per_iteration"], 15.0)

    def test_missing_result_is_an_error_even_after_successful_process_exit(self):
        with self.assertRaisesRegex(ValueError, "omitted benchmark results"):
            parse_results("Static Errors\n", "hol4", self.cases, 1)

    def test_duplicate_result_is_an_error(self):
        row = "HOTARU_BENCH\trefl_reuse\t0\t0\t256\t2560\n"
        with self.assertRaisesRegex(ValueError, "duplicate result"):
            parse_results(row + row, "hol4", self.cases, 1)

    def test_mismatched_iteration_count_is_an_error(self):
        row = "HOTARU_BENCH\trefl_reuse\t0\t0\t512\t2560\n"
        with self.assertRaisesRegex(ValueError, "unexpected or duplicate result"):
            parse_results(row, "hotaru", self.cases, 1)


if __name__ == "__main__":
    unittest.main()
