# Verification record

The production source at `7ec1f013e0ef6399eed2cf46bdee9344152ad566` passed the Linux check with Lean `4.33.1` at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The driver authenticated Bowen Zuo's frozen cutoff-six source at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554` for the reused generating-function dependencies. Run `python3 -I -B check.py /path/to/new/project` from this directory. [Driver](check.py) · [Common supplying pin](../common-pin/README.md) · [Passing hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/46018719102)

The report archive has SHA-256 `6571bfd9e67fba05916cd3ac09e63d2c0701d87790197aaf61e9655ef1250863`. All 24 local staged source hashes matched the exact tested commit. All 11 frozen module readouts matched the previously authenticated common-pin receipt. The seven new modules compiled and replayed with the Lean distribution's bundled LeanChecker. The 12 named declarations report only `propext`, `Classical.choice` and `Quot.sound`. The original-row endpoint is `RepositoryQuotientAudit.original_fourier_enclosed_budgets` in the source below. [Exact endpoint](RepositoryWideResidues.lean) · [Independent statement review](review.md)

| Source | SHA-256 |
| --- | --- |
| [WideDensity](WideDensity.lean) | `ad04ab1e6b1676e090added09e0ff325f4c295aee401fbb2c8459c1bb3abff56` |
| [WideGeometry](WideGeometry.lean) | `a160dc017eb9fffd3b706c5fb53ada876181553b7db5c1816caabffcc346c164` |
| [WideOddMass](WideOddMass.lean) | `74e8a002bc821777784e0a5289daa772a949fe2c65d04f5105f8202fdc623789` |
| [WideOddRadius](WideOddRadius.lean) | `d9329878b14aa60c45739ed59489d47e960e2172cfaa88cb909c245ad9d698ae` |
| [WideVerticalTransport](WideVerticalTransport.lean) | `4f2380548c381100b8c5923cecae84bf6a71060260b2fa646193482698839dd8` |
| [WidePoleChord](WidePoleChord.lean) | `1618663607768d0e950fa1d2a4b2d39186de6d9c3a772e6a9e50c7561819901c` |
| [RepositoryWideResidues](RepositoryWideResidues.lean) | `6d798c2e852bcb6771242c8b2d36eaae90ab87ad7c1ad51f2ae76c6f615ba3d9` |

Two initial jobs exposed different simplifier normal forms between Lean 4.19.0 and 4.33.1. Allowing `ring` after `field_simp` when goals remain repaired both arithmetic steps. The theorem types and hypotheses stayed the same. The passing job completed with advisory tactic-linter warnings.
