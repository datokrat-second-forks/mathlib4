# TASK — OrderDual one-field structure campaign

Repair Mathlib wave by wave until the build is green. Branch `orderdual`.

## Standing instructions

1. **Report the frontier after every wave.** Run `/root/tools/lowprio/lowprio lake build`
   (always `lowprio`, never `taskset`), collect the failing modules from the `✖` lines, and
   report with the script:

   ```
   python3 /root/.claude/projects/-root-mathlib4-mathlib4-git/memory/blocked.py $(cat failed.txt)
   ```

   Report **building / blocked**. `building` must be *strictly monotone* across waves — if it
   is not, the script's import graph is wrong, not the campaign. Lake's `[n/m]` counter and the
   olean count on disk are not progress.

2. **Record elaboration friction in `FRICTION.md`** as it is encountered — each pattern with a
   concrete before/after example, so the cost of the conversion is documented, not just paid.

3. **Interview me about design decisions.** Anything that changes the shape of a definition,
   an instance, or an API — not just the proof of one lemma — is a question for me, asked with
   the alternatives and their costs. Do not decide it silently.
