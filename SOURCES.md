# Source files edited for this release

Only comments were changed (internal names and stale remarks). The first hash is that of the file used in the runs;
for `checker/indep43c.c` and `checker/cover43.c` its first 16 hex digits appear in `logs/<family>/verify3/verify.log`,
and for the generator sources in `logs/<family>/gen.log`. For C and C++ files both versions compile to identical object
files; for Python files, to identical bytecode with docstrings removed. The scripts in `runs/` also had the working
directory replaced by `$WORK`.

| file | sha256 as run | sha256 here |
|---|---|---|
| `checker/cover43.c` | `9f218cf6cbf99f90c20ea644f151ffd2dcdaae3ab6cec13431a2472a37ba4e3f` | `281b739e7c88c230509e1d8c79f1be90437d59c4ebae7be178eea59c3d678c6d` |
| `checker/history/indep43c_v1_b7e3ac4f.c` | `b7e3ac4faba4eaa2848efc4f2d1669e69c60d1dbbfa67ba60f6c3d05ae957bc6` | `4cb1531d9d3fe276e72894365142085437cb6b918930af62ae80364ff3c19de6` |
| `checker/history/indep43c_v2_29c2874d.c` | `29c2874dba0d02a92f48ee37c8646093be354540d4ada3f9c6335d9b6413e243` | `a07e782ca5718bb023bee1ffc9de6421181a4152a49eebc9ae0017dcbce3ecf0` |
| `checker/indep43.py` | `2ca01b628f86d1daf73fee262e45e5c735820dd68f68ddcdda701e1e0b73d7e0` | `e3d31d0030d1590d1b9bb3be350bd80b62d62f7929a02f3814f9bc0657c61753` |
| `checker/indep43c.c` | `90323b1736bec53c1c314f403422e69dc9b8233f675f1c08274952c28c858c57` | `8bf3e24fcbe012024a4162b291d1949d0372abda425b6a6ae808c6c4a9c4b6bc` |
| `checker/mono43.py` | `570e605f6c59f2864872feb2e8fe3f285fcf91ce69268174c7fe180b57ad8aa9` | `57db4831fa7e6010127ae896d702a7807217aed525604fd0b4f9dfb6c9d7e832` |
| `checker/split43.py` | `e5f82e2e6bdcee214a0d4f480a1c5abf24fdf9f25633a6ed939e516759071574` | `a86d0e6b3f4f09ad5bb7fccc093b1d5772107e7c1f36aa453c60f99fae79c10c` |
| `controls/controls_v2.py` | `f67800a8aeeea47f6f170adf6fb37cadbaa5d4049fe691e9615d448a81c9f13a` | `9025b4057f59d4865793355e5403bc31659a30593f54a592a6b3d2003ae84ef0` |
| `controls/tamper2.py` | `f7a0154648f6b83779ebb48ccf45b1a0f8d3946e6ac79c8622f03e09994bb870` | `d7d3a27acfac35e4d9ddc83654eb2357beac932de29d47a3e09fb6216027f937` |
| `generator/est43f.cpp.tmpl` | `b845f64849ac0008abaa84e79cfeb0a9c4391e4513218aca64dfa753db2c1d13` | `3d0cd4d0461913e59c3126ac25fbe4dad5df2b903adc9352d1fe94135bda2b03` |
| `generator/formulas/d_regular_v2/F0` | `41e9ef70480f83daaf1bdd90b085e5b429133ea265e5cde2c5e7dfebe877ac9d` | `b03f78aa2a601e0deccaa8c4f555154c63e6a9f1ef307af9f6f3e1d3d043afc1` |
| `generator/formulas/d_regular_v2/F5` | `4d627a76619bbf7ebb5ef9fa1d37dacc47b443f134a00f7d8549a3c60e020f5d` | `0b8367d696b1e0f103cc0fe87d7ba3d9bf513bd3402b39abde8cc4ba87aefad8` |
| `generator/formulas/d_steiner_v2/F5` | `38c5107e0687f833e15726e4882d194a36ffc04186f86e9ac62832ca514e7f4e` | `349480d6249a4dd284e54d01d943e63e21af1d7c39556ebfd6a0128c5cc7c1ca` |
| `generator/gen43f.cpp.tmpl` | `fd8365de85718a6dbd2202f45aa6050103a35d4891597c24788f1d00b408e53c` | `402c4fb71cf4cfc86b0da496c53dff055eedf260ebcb3e9a47fee80c9fac6d21` |
| `obstruction/tools/ceilpt/ceilpt.cpp` | `54481d50ae47391b218b0cbb80484e4f69bb0967c6070a38d4cdd639bf142819` | `696f04bc55dec91a02f00b77c520b64b935a58c8b22fd543530ede0e734fa11e` |
| `obstruction/tools/indep43.py` | `2ca01b628f86d1daf73fee262e45e5c735820dd68f68ddcdda701e1e0b73d7e0` | `e3d31d0030d1590d1b9bb3be350bd80b62d62f7929a02f3814f9bc0657c61753` |
| `obstruction/tools/mono43.py` | `570e605f6c59f2864872feb2e8fe3f285fcf91ce69268174c7fe180b57ad8aa9` | `57db4831fa7e6010127ae896d702a7807217aed525604fd0b4f9dfb6c9d7e832` |
| `obstruction/tools/obstruction.py` | `084768e74ffde6d982673a5ebe93d5787a6c8922d02dedce7c9fa0e2ded06dfb` | `d9552682266e873f07d15e07b40155df66dc632ccaf255b049f732b170e0ea5b` |
| `runs/controls_real2.sh` | `edbfd1db4a3f9b86d5c32c2e3a5dc827f62b10fa70bbadc94d93979ad42cabb1` | `e52b4a2d485bb737fb48e2337fff39f8fa5931aebb3a1bafd2e46b9a76496913` |
| `runs/run_cert2.sh` | `bc0f0d154e5f5c719d0e0038268cb5beb4c021e5a45a70f7087bd299688ef0db` | `c5e59553854a7f89e55826068c567876a2003aa3127e6aff03b3172b89433142` |
| `runs/verify3.sh` | `73b82d848f2109cd2c7e38a9c3f16b8160ea542600e776b0769568e7e2a3fd60` | `cc405dcd4b2fcbb3609de91c20c8a61d2f7fbffa787bcdc3dd398317ac74cd15` |

In the logs, `<WORK>` replaces the working directory and `<host>` the machine name, and the first line of
`controls/audit_crafted_records.log` and one phrase of `controls/controls_v2_with_v3.log` were reworded:

| file | sha256 before | sha256 here |
|---|---|---|
| `controls/audit_crafted_records.log` | `6a76cbf22df2ceaeb08e825220a1b4b7a8d2e01b884c372e6c5b777eb0c38a15` | `a9e42e6ca3246e342f8aa0de3fada016763cc9e26cbbdf463b3696cca8c70e7a` |
| `controls/controls_v2_with_v3.log` | `72422f5f0fecb397d218d7e2243a46fe7ed4b4b7c03f4096361a2a65eac476e6` | `680af93880d12c5f94feaf8041e497d32e2cdd3ecbe7c4b406acd82b47da8865` |
| `controls/ctl2/cmds.txt` | `c03feaf4703da47ba07d8778a8deefdb6e1d7736bbf71a9738fb27b8a5bd2184` | `d42427d220ff1b7ee93c62179ec07058d9ab9efcf98fe5e3dfe2540753e3b597` |
| `logs/d_regular_f_ge_dv/gen.log` | `70739138d51cfa8082d00999d244a1b69606b355a045cb11df1154ef9ed7e177` | `afea14d5c91d17639ecfe84558f19ba543a55a72cb4e54e3c144a844cff08ea0` |
| `logs/d_regular_f_ge_dv/gen43f.cpp` | `3191d5f100d2b2c47ba5bd914beb7a734bdce78ba53c7d543b3f6320cdbe0bdb` | `bb512f014d8b496b41f1ee57be2608e12fcbd3de9da65d8b960ea6a92608f0b7` |
| `logs/d_regular_f_ge_dv/verify/cover.time` | `a62718c51ca523095df03813c92e369705d93a9730a5693ab1129c445bacb04f` | `62b53c001fd33b1f4049c69dcc3244505bfb66be59c1d03be493ab8cbe17cf1a` |
| `logs/d_regular_f_le_d/gen.log` | `1127388e136f044230513da425f80e871290cc62156b36cbebf7fc45800ce6af` | `c0d6dd2b45154bf7ee885426c9ff66c10f7f4635be1f5c44ae293e59242d672b` |
| `logs/d_regular_f_le_d/gen43f.cpp` | `3191d5f100d2b2c47ba5bd914beb7a734bdce78ba53c7d543b3f6320cdbe0bdb` | `bb512f014d8b496b41f1ee57be2608e12fcbd3de9da65d8b960ea6a92608f0b7` |
| `logs/d_regular_f_le_d/verify/cover.time` | `8c2e321e7104e460b501d982bc8ccceb98151f43e40b26e1178de4ed2299611a` | `935dcdb27253f64ca41638553179c60417ee1ceed62403e6e9f1f41ac29c4b6a` |
| `logs/d_steiner_f_ge_d/gen.log` | `b7ebb7b00a57edfa3a0cfc1ba20a28b14b79cc1e4cee00f2614c9b5349d460eb` | `798a91bea35fc176750e6b9c1dd1e300a78b90ce12bd3d067cf05ccc227c6177` |
| `logs/d_steiner_f_ge_d/gen43f.cpp` | `3191d5f100d2b2c47ba5bd914beb7a734bdce78ba53c7d543b3f6320cdbe0bdb` | `bb512f014d8b496b41f1ee57be2608e12fcbd3de9da65d8b960ea6a92608f0b7` |
| `logs/d_steiner_f_ge_d/verify/cover.time` | `90d36826fdac8bef2f23105ae9aa8b7526478cc76629553031a1fe3956cd627a` | `8232937eaeb8ca7d31457e5f55a9fd047357be61853c112eadfd1eccf6700eb3` |
| `logs/d_steiner_f_le_d/gen.log` | `0d560c9846704b69004e751f0a7fe7e79d1291cb8e1e200fe25adc9063a934ab` | `5de033612736d40b91bdc286b09f773f6fc29255ae79ede259f3ea7007c504b3` |
| `logs/d_steiner_f_le_d/gen43f.cpp` | `3191d5f100d2b2c47ba5bd914beb7a734bdce78ba53c7d543b3f6320cdbe0bdb` | `bb512f014d8b496b41f1ee57be2608e12fcbd3de9da65d8b960ea6a92608f0b7` |
| `logs/d_steiner_f_le_d/verify/cover.time` | `a804c7ea069d88bac32c59aa719c4e95d92132715d85edc9ce8681bed7570e19` | `dc5034fff35220048ae7816ea5960be96c58454fa669ec6f56711fed54576cac` |
