An artifact for CCris. This work is based on the Verified Software Toolchain.

## Where to find code:

| Section                                                         | Path                                                                                         |
| --------------------------------------------------------------- | -------------------------------------------------------------------------------------------- |
| 3. Environment Predicates                                       | [veric/env.v](./veric/env.v)                                                                 |
| 4. Expression WP                                                | [veric/lifting_expr.v](./veric/lifting_expr.v)                                               |
| 5. Statement WP                                                 | [veric/lifting.v](./veric/lifting.v)                                                         |
| Theorem 6.1                                                     | [veric/lifting.v: adequacy](./veric/lifting.v)                                               |
| Theorem 6.2                                                     | [veric/lifting.v: guarded_stop](./veric/lifting.v)                                           |
| Theorem 6.3                                                     | [veric/lifting.v: wp_adequacy](./veric/lifting.v)                                            |
| 7. Using CCris to Verify permute                                | [progs64/proofmode_test.v](progs64/proofmode_test.v)                                         |
| 8. Reconstructed VeriC                                          | [veric/](veric/)                                                                             |
| 8. Reconstructed VST                                            | [floyd/](floyd/) for VST-Floyd, [progs/](progs/) and [progs64](progs64/) for VST test suite  |
| 9. RefinedCC typing rules                                       | [refinedVST/typing/{programs.v, int.v, array.v, bytes.v}, etc](refinedVST/typing/programs.v) |
| 9. verification of the permute function                         | [refinedVST/typing/automation.v](refinedVST/typing/automation.v)                             |
| Theorem 9.1 RefinedCC Adequacy                                  | [refinedVST/typing/adequacy.v](refinedVST/typing/adequacy.v)                                 |
| 9. Demo of end-to-end verification with the RefinedCC toolchain | see [RefinedVST.md](./RefinedVST.md)    "Running the frontend"                               |
| 10 mixed mode example                                           | [progs64/mixedmode_test.v](progs64/mixedmode_test.v)                                         |


## Installation Instructions
For CCris (and VST): [ivst.md](./ivst.md)

For RefinedCC: [RefinedVST.md](./RefinedVST.md)