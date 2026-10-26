# Files whose comments were edited for this release

The proof was built from versions of these files that differ from the ones here only in comments (Lean), in comments and
docstrings (Python) or in comment lines (shell). The one listed exception is in `assembly/axgate_v5.sh`, where the
default of `AXG_FROZEN` (a path of the build machine) is removed, so the variable must be set. The census file differs
only in its first, comment line. Every Lean file below is identical to its built version once comments are removed
(`tools/lean_nocomment_v1.py`). Every Python file has the same syntax tree once docstrings are removed
(`tools/py_nodoc_v1.py`). In addition, the checker and the proof chain were built twice, from the files here
(`tools/build_chain.sh`) and from the built versions. A dump of the name, type and value (proofs included) of every
constant of the 58 modules, 7,563 constants in all, was byte-identical between the two builds. Units compiled against
the checker built from the files here gave byte-identical `.olean`, `.olean.server`, `.olean.private`, `.ir` and
`.ir.sig` files. The 25 files of `chain/n2m/` were built as module copies of the `lean/` files as they were before their
comments were edited for the `lean/` release. They are shipped as module copies of the files in `lean/`, made with the
same transform (`tools/to_module_v2.py`).

| file | SHA-256 as built | SHA-256 as shipped | edit |
|---|---|---|---|
| `assembly/axgate_v5.sh` | 673b2088cc3d215cf64ad3f0bb2507858d8769906aafe55adc2b87b9000f76bb | be4defce0e51c3ec231c1ae1912e497d3094372869f7534db7e357532e061afd | comments, and the code edit described above |
| `assembly/build_agg_v2.sh` | 064bdbcdc92bde04ba567fe4bd929185f580d7ef19998d3d20447eeebddb6df5 | 4318e394046f15f3493434b9e5095786d3636b51b21196c452537209643169a3 | comments only |
| `assembly/gen_agg_v4.py` | 2a7469128138d5d09fa6f59dc86e7e06a249f2d929d1b1855e5c89dd57731db4 | b08e44bd5c959119ad97a5aa9af1cdd3907f41da270c4790b61b0de41987c15d | comments and docstrings only |
| `chain/n2m/S43/IntervalSound.lean` | ebc4c67a14e5a587846d0155646613fc62236d3b3434c1514a4160a2453047b4 | 4ff6c6cfd9a053ef58473dc2310f357ae2dac078f44b7f215affe4ddd43dcf3c | comments only |
| `chain/n2m/S43/Sound/Affine.lean` | afba275d61272613e84f78f319df3e360830df4f827e2f0acc7a562dba1ef2ca | 1198d0e1ed0af1f2b21a712c546fdebedf7909a10250783791dbdb8415e1eaa5 | comments only |
| `chain/n2m/S43/Sound/Box.lean` | 5398f7c707fb929cd8633753c755d305ba47c2d33d21014fd39bb4e9e6f7a6e8 | e8cbb61f747e3e921201b8a576322921f2a957ccf9a892bbc90ee75e96f39309 | comments only |
| `chain/n2m/S43/Sound/Bridge.lean` | 8a6e1df557c2861092ea02d3727d34dd3f5ad4ccbd5bdfdc66f282ce2f1aafe1 | dbe3b871a1e6a17e6c0d5e9c0bfd327d6c8db80ca1af2d0b1f548f124737b8c1 | comments only |
| `chain/n2m/S43/Sound/Bump.lean` | dbbac43fc8b68eca275cd35d40cfb4bb0b9023db59e5be736593ce7abd6fb562 | af3ea853a93d3adbf5b5a4f1c6a5db29eac5ddc378e9585d90dd1c7712eaff18 | comments only |
| `chain/n2m/S43/Sound/Case.lean` | 61b9686ccab75710969d6fb8aac6a36046be700f51f50e61934efb42dfeea329 | 501f754a4abe5be90c970d55fe423b51d10c3afd258fe7e8b3e3c967ae683dbd | comments only |
| `chain/n2m/S43/Sound/Convex.lean` | d4f6e1c42a8ca505eae3303a2457426ce7b6afc70c0eedc773f10ba8b55fbc4e | ebd478075bea7aa5a4c4fce50d4f04cd4bbc4de12a6fc4df54d3d1685986c553 | comments only |
| `chain/n2m/S43/Sound/Data.lean` | 196e26f04114c9ead9ed60e80d76ce9b3f68ccc2005d3223b0dc9390f6f9f32e | ed772d3becb697ba0aae435cc07114e1b0b102c99c89a10c4f73bf3a985a0e4d | comments only |
| `chain/n2m/S43/Sound/Enc.lean` | ba2f853d3132bbc9c8f4f0130c3dc9f2311ceb71249532381180906345ee7f42 | 270aa932ae69ea549289cced447e8acfda3a2aca4d334bf9b251c0b81269a4fe | comments only |
| `chain/n2m/S43/Sound/EvalSound.lean` | 3a4e69adf090b4492a164df73a79725a3792b0fa10719660da9d71affdbdc841 | 6f082eba6878c759292b78b95986c70ab107dc36259d5f98dfe8d7c3a01a2e4f | comments only |
| `chain/n2m/S43/Sound/LemmaSound.lean` | 336e6cc6e902e728e7903393fe96af6e066568fc6be73041f878c35e395fdb50 | 432f7f62aaaa5c5856eddd97913940439ed980b9a416930f271eccd65dba31ee | comments only |
| `chain/n2m/S43/Sound/MainProof.lean` | 3750785366bb75b6c5ec30590c8b62da65148ee541c848e5715f3350d912a0a8 | 30d39a952f6590215171e580080002c292ef47b90b8d6121bc30318ce205a0b8 | comments only |
| `chain/n2m/S43/Sound/Net.lean` | 99761400b4e85a56ffe31f665727f437f38d623201bd0bf706cc1d87f7838876 | 32a6dc7a3494cb5429e5179e510ecb9d0d968c2667a7bc352cde7f717d905982 | comments only |
| `chain/n2m/S43/Sound/Record.lean` | 23c7823213153e7e0c479ed94bcd5666a829e00fd901086f1b86e4105e17c1d9 | 2120a24f7bf902b5ad1d1da881f55d8a122d694f831351b1ac7bd9708523d01c | comments only |
| `chain/n2m/S43/Sound/Target.lean` | 66337e23bcf847c3d71e56ed8bea1a923b90cc27c9561bb98ed24486a68c5f31 | eba53e46e269dec316e9a93f97954e7f257c6bc5e3c8b0ecd8becdc4ed810adf | comments only |
| `chain/n2m/S43/Sound/Unbounded.lean` | 7f3dd0fbdab5e3c5080feb62bdc993a326fe5db5bbf6327e0ca144778f74c33a | d189410a4f0d3ddbd810c49b44d672b633d6e1ba06d77534ac282c65f6c9da79 | comments only |
| `chain/n2m/S43/Sound/VertexSound.lean` | 89cd63e224c6f2c5fad929cff4077853d4b7f839858c38ffe4555fd283866949 | 2059b904d81088d9c76b39c775442c9c0c066239b14351a8bfed02eea3941d58 | comments only |
| `chain/n2m/S43/Sound/Walk.lean` | 4cf14e0a762b187a3103d4d2b886305fa53b0ada91be16bdefe44df934bb1aa2 | 1eb81660c479fcea2cdc3282b23acb52ca3802b744889e5ff4677f3fd95a3ede | comments only |
| `chain/n2m/S43/Statements.lean` | 6081bc1df525673ad4ce6d9f2785171e98bf1d68ae8bb7d54c3f9be235c2f09a | c99c46512a5581585d5b3f62d5ff6da18b723ea3dd5f98a0e61b0167fe0f9c90 | comments only |
| `chain/n2m/S43Core/Check.lean` | 2361e29a57f023dbbd9c2d0253d9efbb4288c5939c400f0c94eba6715e4266e4 | d24aee01b8fb27b16cab74d7f6d117b259e972941363696385610fe88c9ca3ec | comments only |
| `chain/n2m/S43Core/Geom.lean` | 65d3fb5d8d89c456f5b8d4ea4307082b0a59894468376fc5f343779a7bd8ab73 | 0eee7b79ae8ea924ff0e2448e1dee13d951c96a1e93848923546687b309454e9 | comments only |
| `chain/n2m/S43Core/Interval.lean` | f37d1d263200b0bf59beee602386cc82437e34f5e051f866356f7468cf0d007c | e6a9017d9b56ccb47e1f7d960dd4ea3a17f10154618c2dbba0361efe01322bb0 | comments only |
| `chain/n2m/S43Core/Splits.lean` | 4c948c76028a2b730d8c937698e9df95239227f68c4209617b1886790d840434 | 3a8ee18a172ae26f36383a1fa088abba9853050700b651f3f7d03891f46c45e7 | comments only |
| `chain/n2m/S43Core/Tree.lean` | f12f9eaa1d4fd0732cda3b1978a7b9af8886cfc962271f5147cabc234fe87a71 | fd9ea59bdf9b7914f17471b337d7705e7d83d85fa8acf8a217cb27a360907730 | comments only |
| `chain/n2m/S43Core/Vertex.lean` | ea368fd267551eea8fae73eff96670c8c104480eb1cccd00c6ceed03c7ac6c58 | 2deb94bbddf4345e16787c82646b9919bd1bd7bfdb739361e1aee2af621ac640 | comments only |
| `chain/src/AggLibK.lean` | ca670e65069c8f6ea64a906fd59d9ead8743335356c5410862f6bf0d79c744e7 | 7eb27473aa90b490b0d319f2abddcd6c31a83eeb74c155c75d33bd735f099d9d | comments only |
| `chain/src/DNBound.lean` | 39aa7f66cfdf6d9f90fc2132af1abdbbf9a025c28cc2c66428d82a728731422f | f7cbeab9cfc9e48307e065040169b503f10511ab900a84a6e497cc128762dbf3 | comments only |
| `chain/src/DNSim.lean` | d1cf05858508ba81b8ce445ce8439bf22cd21666c921ab4bd1f0379b1522c4dd | 3ecec622db5354a87fa09e787b26aa630a5171993bcdc13ac6551947be644b8e | comments only |
| `chain/src/GeomEB.lean` | 1ced3866a3b4d1043d2b0a46f51a9e2e0a2de134bda34c0fa98b8e87f3705c2a | 8d093fde7650ec14476760bc52fbaa6e4467d42304e908845fe702a9bd0b7958 | comments only |
| `chain/src/GeomEB2.lean` | 12f1411a264ee07454588005b2db1c84b2f3ebddc0d66c206738bfb01894aef1 | 80b3141250fb38ae4728e8de6a732b5303d2fd8616f21cdefd302e95dd948d1a | comments only |
| `chain/src/GeomEB3.lean` | ee9b82834d8a5f8047fcde0b1c64150d1543fa8fde27bc69f447784e50592471 | f91bce896d32e516da5e721a3a2188b4fa8e331574ff00301f712184674623aa | comments only |
| `chain/src/GeomEB4.lean` | 24cf4643b5928219e99625778e21212383964ec2dcfb27235fd56f8dcac06eb1 | e4587be3bbcfcab6b286d886f69906b711a74f2a08d5c615d1ba8045e4ed0cd1 | comments only |
| `chain/src/GeomEB5.lean` | 3a40186b064e6710dc30bdfaa532e74ac3743c5cad69eeab015924634ce1fc45 | 5d935d1167a14399a932f2dc4b2ed74f30eb026a9257fc8ec937f8da00ce887d | comments only |
| `chain/src/GeomEB6.lean` | 422b177de1725a451fadb5604c6042663769059b08f59007eeb204f1033c7eb3 | c6679018a2b66a0b3d6664c1d382c942b0584a5d981d909d4c8e89d6a9cb6626 | comments only |
| `chain/src/GeomEB7.lean` | 6b2a4ec94e1e64a8fb0bcd1d767ea8913484aa0924bcdb715889b1889a416da0 | 1f8604f2faaa921764930af663430f2feeb31df686cd4f7c7af3c64404b6356b | comments only |
| `chain/src/GeomLem.lean` | 7305415e87582ef4844edea3a4b77f6a751a32380e544878f42ec52618a98514 | 9cbc8b59b3bbceb80b174feb6fc413b94669da73f247c57dce3f044ba7c458c7 | comments only |
| `chain/src/K0Bridge.lean` | a5e42d066828bb2e90129a967d5f68ffaf67a6c68cd215c87c48bdcf0e151567 | 5e95da5b4ee21c6ae87298bf4256be27ffa9ae04b357a870c5b8c71ec947cc55 | comments only |
| `chain/src/K0Lemmas.lean` | 6b55294a0f3e523bf7a49ebd895c9f1d2207f133d480635165a5a285e59c9eb9 | 3e670c6497f8291bc4d797dd747d8095d9ebf3d0a4e634e28829ee8f7fb75fa1 | comments only |
| `chain/src/K0Lits.lean` | 95b4dd4621ec2003a433b4f9577bd61de79a7fc04d0f484cbc052dde42165752 | 4f47d27db4b9b6d78178e3cbd9b80cde68f7b086260f868fb69721429bd83bf0 | comments only |
| `chain/src/MainKRoot.lean` | 5345ef82d5cb93f6f9094384f63a968e086295462c438f4b1dee7ac520e7cde2 | 40e25813161a3fe30a396bb6290f153bcdb6bb74372e35c92fb73718d9bcd6c4 | comments only |
| `chain/src/MainKTemplate.lean` | 722df9388ced22ec2ba04445845aab882fe5febcb4c5d8554d0cd7b6dd857d74 | 5644e59debe5370f0a7da85f7c003c98a7a97a58675ef6e955e1dd695a972b2b | comments only |
| `chain/src/OpLayer.lean` | 49af874aa1cc176cac97d895120262230ccdee1335bccfdba10a9739b7322ceb | 0d5837bd2fcd235a02c9ecfca72a164063332564f19b0d9bb95ea612534dbd21 | comments only |
| `chain/src/RecordK.lean` | d48a7c4b690d9eb472a698cc63db0ec4d93d59beeae3585a74afffceb65bc363 | a1a6faea9ffbe1825fde0fc204c3cc3bc9b07810aebb1c363eb7b01a1b7ed207 | comments only |
| `chain/src/S43KChainU.lean` | 71cb8b4bd1034a8c36546f46f20043cdc5d93f3c689ffd7789feeaae3eb8ce28 | b9bb4215df1ef8eb2b51d82a17e86503bca5d727af10ae0eedc4eab86c75e254 | comments only |
| `chain/src/SplitsGlue.lean` | 76353c2ab6a53880cec91afee3b20c34ec5038c9100f47498d6c4834ffbc9fd4 | d34a7958dd6d05b05debf7ebaa90b6bd95c27f3a8e6d36c10a98b3d116a26956 | comments only |
| `chain/src/SplitsGlue2.lean` | 9213d716100d69676a431793e8f214dc517abde371740cf5f7a4e761beb5231c | 9465116b65b8057adfde4da771bf16bbecb4b31e38783e3f84e83f423672bfad | comments only |
| `chain/src/VertexSoundK.lean` | 238f79f0b673eeed2ce547bb14aa2ca8a2a981217ea140d67cd9ae85e925ef1f | 907c527244ba020d8380c0df62362cd29eda4d1769d59bfa4575357cde5c5134 | comments only |
| `chain/src/WalkSoundK.lean` | 8a906dc19bc9e65de49caf982fc19d67aa0010fb316663dcd8eb411031efe15c | 47741d030f365130234c6f04b6fdf014a9242ef1819ffdee0c943456e712ef70 | comments only |
| `checker/S43CoreK/CheckK.lean` | 59921566f6e4e4484f66201303bcadb38478ef1f1ce0ee26dba1072ecb65d9ce | bf1e7a394898086c383506f6ce84a863453ce1ccc24e9db7946822b7cd77ba97 | comments only |
| `checker/S43CoreK/DN.lean` | 6d9597f65a43adf59cd1f02190b7d6ba7ce9575331fe71211e9ff6d1c84bf388 | a0ec2f3d62b6d3c3060cecc501d1ee18cc2ad72c280e5b335976e9ea923f6a23 | comments only |
| `checker/S43CoreK/GeomK.lean` | aa1928091f31296b003b0a8bb3ba6aefadf439ab330768fa3edf588007ea1c1c | 3abbdabda99ad582e0dc0485f1933c6ed915dae1394ffe56c004423a1c4ca60d | comments only |
| `checker/S43CoreK/Ladder.lean` | ae269fb04b710d98b326ff3ffda12495b9b0b95f525c928fff96de04f60bc0a3 | 4606e75e9ca9c6e3cae9cd121f3a88dbbbb95794943d327358101bd05e793a5b | comments only |
| `checker/S43CoreK/SplitsK.lean` | 29d4f303dd73988a5091b31d419110dab560a3abf85aa8a8aaadabde7633638c | 396095a8c1154b6f9461752464e4792936dc1e65d8720d8ff93c82cad31f7a56 | comments only |
| `checker/S43CoreK/VertexK.lean` | f8505b225027a375fcc370a370f67267c3f68263feffe4ddf8063434e50a85b8 | 0e6418630fd16ce3cc390f3cfc1184748bda684996a44b3109ccf7fc9ea2f7a0 | comments only |
| `checker/S43Walk/SkelK.lean` | d7ea0c89a8e3a58f9ba07e317f4f7fc36d1c163e9161fd0afbee3ccf142a5612 | b03961dde082bc80bb176fea35dbc6c73e8646f2c119b70dfedf1ec647357e65 | comments only |
| `checker/S43Walk/WalkK.lean` | 95f68616d3bfcb03ae331652d80a781ee380fda9c6a0fd16f0174ae65c6538e5 | ab6082f6d0a0097957a036d8ab7ab40dfc766dee05cb559e70e6f7f1af500dd0 | comments only |
| `checker/S43Walk/WalkK2.lean` | 7997881ee8e1cc8bd112518bb0b9558c4c0343bdb10e869917f1f6b1708e6389 | 465e7f55699979c2ab1e8ca1bb04f8f612c681bf7a6e1a44520d962c2ac2840d | comments only |
| `final/S43KFinal.lean` | a5a0478d61c6aa10ec4078a3e369a05a97dc21593153f7f7fd1c7db5b8b634f3 | b914bafdb6b0ee72f8c28a54acce215a007663a4c27663a88e8b869b2fbe1f92 | comments only |
| `kit/CENSUS_jobmaps.txt` | c72864e378bb6c90f0b3dc4c2dbdceb27f580b594d66ae4180f62e02ada627a9 | ab3d043f56a6957086b8b2a4058eae1dca47a62341d4433580a2626b8e679570 | first (comment) line only |
| `kit/gen43k_shard_v4.py` | f391f3e3d2e69ae0c7d2579c42ef8ac3df46535dcdf7c1acc2b1416603542b9e | ead59927c293be6aeffe277d761eb4185535af8593446456b0d548218b63307e | comments and docstrings only |
| `kit/jobmap43k_v2.py` | 8f41939cd20ac6c2cb07979511b369e602bf90504a4df5fa2c9cd1375f58ab3b | 58b2e5060656a3ade188db246e39dfaa4b245138cfa6b71a8d9d66cff9a439f3 | comments and docstrings only |
| `kit/libbuild_v2.py` | b7188262c19b3d364fb6423b5c6710b398cb911c1774cf2bd19bdf17012caa45 | a179d9fca2c40365bcb9e320e840c28872cd5aab554cd887199fd3c33f19a23d | comments and docstrings only |
| `kit/walk43_v1.py` | 689da52a0545bea4ec2f78fe1a2a85ee531e65030aafa914dc5cf40e271bd03f | 3ef8d6b907fefb347d8c6a5e66f090ddf5f2f34eced935547ca72396963dbc07 | comments and docstrings only |
| `tools/to_module_v2.py` | 4ce9f32c1b339c51f9152fa6f87a4eaaf4515ff4a3eb23c278c1e344ecd71735 | b9f28024fcb44c7cb3ac029b08e8fdd0cfa2d3a24641410e462c3b4c0fd8be82 | comments and docstrings only |

All other files of the build that appear in this directory are unchanged. Files here that were not part of the build:
`README.md`, `SOURCES.md`, `SHA256SUMS`, `kit/COMMANDS.md`, `assembly/README.md`, `tools/build_chain.sh`,
`tools/lean_nocomment_v1.py` and `tools/py_nodoc_v1.py` (written for this release and used by the checks above).

## Final module

The SHA-256 values archived in `lean_kernel_lists.tar.xz` for the final module's output files are those of
`final/S43KFinal.lean` as shipped. Compiling its built version, whose module comment differs, gives the same `.olean`
file but different `.olean.server` and `.olean.private` files. The table gives both sets of values. A comparison of the
two builds at every level (imports, constant names, kinds, universe parameters, types and values, theorem proofs
included) found no difference.

| file | SHA-256 from the file here | SHA-256 of the build of the proof |
|---|---|---|
| `S43KFinal.olean` | a9919b66bce04794f9b4262a3a2dfdf732ee92f343a690cc22e2c25272eaa588 | a9919b66bce04794f9b4262a3a2dfdf732ee92f343a690cc22e2c25272eaa588 |
| `S43KFinal.olean.server` | 21e5159c91dd658ff2f90f81735d1c1443f420ff922fa587807b1959f4e3740d | 966297f4946bfb06b8a5d69ce58b8b354fb008c6abb4218262cb408252c080a5 |
| `S43KFinal.olean.private` | e5f9de896eaf8ae5e3961c1d4ab4864d09a59c528d3575c1a7279193272d14fa | 9557a25ba178ee28df5ad2e7cc3375bce8c29ffd21c1e25e41264e8907f51aa7 |
