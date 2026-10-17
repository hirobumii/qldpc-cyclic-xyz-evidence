# XYZ56 / XYZ88：两个有限实例的 Lean 形式化

本目录用于复现原始 56 比特和 88 比特候选校验矩阵的有限证明。
形式化对象是**忽略整体相位的二元辛 Pauli 空间**。

> 最终状态：通过。2026-10-17 的独立隔离源码构建核对了 59 个 Lean 模块，61 个步骤全部成功；22 条最终定理的类型和公理依赖、6 条语义回归测试均通过。最终源码哈希与冻结清单一致。

## 1. 最终定理及其准确含义

总入口是 `QLDPC.lean`，聚合入口为 `QLDPC/Parameters.lean`。
参数谓词在 `ParametersCore.lean`；两套主定理分别在 `Parameters56.lean` 和 `Parameters88.lean`。

| 定理 | 二元辛意义下的结论 |
|---|---|
| `QLDPC.xyz56_parameters` | 原始 56 比特输入满足 `HasParameters l7 24 4`，即 `[[56,24,4]]` |
| `QLDPC.xyz88_parameters` | 原始 88 比特输入满足 `HasParameters l11 36 4`，即 `[[88,36,4]]` |
| `QLDPC.xyz56_distance` / `xyz88_distance` | 对所有非平凡逻辑 Pauli 的重量下界为 4，且存在重量恰为 4 的见证 |
| `QLDPC.xyz56_geometry` / `xyz88_geometry` | 分别有 35 / 55 个给定校验；每个校验重量为 8，每个比特参与 5 个校验 |

`HasParameters S k d` 同时要求 `k ≤ n`、所有给定校验两两辛对易、
原始生成空间存在大小恰为 `n-k` 的线性无关生成基，以及精确逻辑距离 `d`。
这里的秩为 32 / 52，并非未经证明的消元程序返回值。
定理名中的 `geometry` 仅指校验数量、重量及比特参与度等稀疏校验结构；
不包含欧氏空间布局、中性原子阵列实现或物理几何约束。

### 对象和证明结构

- `QLDPC/Basic.lean`：Pauli 是两个 `BitVec n`；加法是逐分量 XOR。Y 在一个位置只贡献一个重量。`InSpan` 是由零、原始校验和 XOR 归纳生成的完整空间。
- `Candidates.lean`、`Binding.lean`、`Geometry.lean`：原始支撑列表、位向量字面量、索引合法性、循环立方组合构造和稀疏校验结构。
- `Commutation*.lean`：有限输入的两两辛对易证书。
- `Rank*.lean`：32 / 52 行基、双向换基证书、主元坐标恒等矩阵，以及任意生成空间元素的唯一二元坐标。
- `DistanceCore.lean` 与 `Distance*.lean`：将任意 Pauli 按非零支撑分解，证明 syndrome 等于各单点 syndrome 的 XOR；有限证书排除所有重量 1、2、3 的非零 normalizer。该桥接证明覆盖任意 Pauli，并非只测试列出的错误。
- 重量四上界：原始纯 Z 四点见证与所有校验对易；一个与校验空间正交、却与此见证反对易的纯 X 对偶向量证明其不属于完整稳定子生成空间。

## 2. 信任边界

使用官方 Lean 4.19.0 随附的 Core/Std，无 Mathlib 或其他外部 Lean 包。
有限证书采用内核检查的普通 `decide`，不接受外部程序返回的布尔值作为定理。
禁止 `sorry`、`admit`、自定义公理、`native_decide` 和其他原生计算信任捷径。
生成脚本只是生成候选证书；数学结论依赖生成结果通过 Lean 检查。

标准逻辑公理与新增经验性假设不是一回事。独立构建核对了 22 条最终定理的类型和传递公理依赖：
两个参数主定理和距离定理的依赖恰为 `propext`、`Classical.choice`、`Quot.sound`；
校验结构、秩和见证等辅助定理只使用其中的子集。
完整独立复核输出保存在 `audit/final-build.log`，机器可读摘要在 `audit/final-result.json`；
开发构建的相应输出保存在 `logs/final-axioms.txt`。
`Audit.lean` 可再次输出主定理及辅助定理的传递公理依赖。

### 原始 JSON 与 Lean 字面量

`data/` 保存两份原始 JSON，未改变原候选的置信度字段。
SHA-256 如下：

- L=7：`c598183c0768f29abffb430992543ce3cd7ddbb1337be0701c7db5ad88252c45`
- L=11：`353865b626ea7205b62e5fcf0826b4aa453f506d28330c6291fcf1d8344ffefe`

Lean 证明的是源码内字面量对象，以及支撑列表与位打包对象的一致性。
**JSON 解析、文件复制及 SHA-256 计算属于外部边界，尚未在 Lean 内形式化。**
`audit/check_literal_binding.py` 不调用生成器，独立比较 JSON、支撑列表、位打包行和重量四见证；
其实际结果见 `audit/literal_binding.json`。

### 未形式化的部分

- 带符号 Pauli 算符、复 Hilbert 空间及稳定子码实现定理仍属外部解释。
- 独立脚本核对了本例正 Hermitian 代表元的关系不会生成 −I；这不是 Lean 内的相位一致性证明。
- 形式化结果仅覆盖这两个有限输入，不包含整个无限族、渐近参数、内禀非 CSS / 局域 Clifford 不等价、文献新颖性或最优性。

因此，将结果解释为量子 Hilbert 空间中的码参数时，仍须使用上述外部稳定子对应。
本包不将这一步误写成已形式化的结论。

## 3. 从源码复现

### 环境

推荐 Linux x86_64，Python 3.10 或更新版本、Bash、`curl`、`tar`、`zstd` 和 `sha256sum`。
Python 脚本仅使用标准库。安装脚本下载约 344 MB 的官方 Lean 压缩包；解压工具链需要额外磁盘空间。
本源码包不携带工具链、`.olean` / `.ilean`、`.lake` 构建缓存或审计临时源码副本。

工具链版本、官方下载地址及固定压缩包哈希详见 `TOOLCHAIN.md`。
哈希是对下载文件测得的复现固定值，不是另一份厂商数字签名。

### 普通构建

在解压后的项目根目录执行：

```sh
python3 scripts/verify_bundle.py
./scripts/bootstrap_lean.sh
source env.sh
python3 scripts/check_sources.py
lake build
lake env lean -j1 Audit.lean
lake env lean -j1 audit/AuditSanity.lean
```

`verify_bundle.py` 适用于发布源码包，检查其 `SOURCE_MANIFEST.json` 和 `SHA256SUMS`。
工具链由安装脚本放在本目录 `.toolchain/`，不会安装到用户主目录；`source env.sh` 只影响当前 shell。
校验模块串行导入，文件内关闭异步 elaboration。有限证书编译可能较耗内存，
请勿同时启动多份完整构建。构建耗时依机器而异；实际记录见审计日志。

### 独立的顺序干净构建

下面的命令在新快照中复制源码及输入，不复制开发目录的任何项目 `.olean`，按依赖顺序逐模块检查，
最后打印指定主定理的传递公理依赖，并运行独立语义回归测试：

```sh
python3 audit/run_fresh_audit.py \
  --snapshot reproduce-build \
  --theorem QLDPC.xyz56_parameters \
  --theorem QLDPC.xyz88_parameters \
  --theorem QLDPC.xyz56_distance \
  --theorem QLDPC.xyz88_distance \
  --theorem QLDPC.xyz56_geometry \
  --theorem QLDPC.xyz88_geometry
```

结果写入 `audit/reproduce-build/`。要完全从头重新实验，请换一个新的快照名。
重复使用同一审计快照时，脚本仅重用该快照自己编译且源码哈希一致的结果，
并使发生变化的模块及其依赖者失效；它拒绝使用无审计标记的既有目录。
默认复用官方工具链自带的 Core/Std；“干净”是指不复用本项目的编译产物，
不是从 Lean 编译器源码重建工具链，也不是用独立实现的内核再认证。

### 外部独立检查

```sh
python3 audit/check_literal_binding.py
python3 audit/independent_candidate_audit.py
```

第二条命令默认只检查包内输入，不重新比对原研究目录；若另有原始目录，可传入 `--original-dir /path/to/original/candidates`。
交付时的报告保留了当时逐字节比对原始文件的证据。

这些脚本会刷新对应 JSON 报告。若要保留交付时原始审计记录，请先复制目录再运行。
它们提供独立计算佐证，不替代 Lean 的通用证明与内核检查。

可在不改动工作源码的前提下检查四个生成器能否逐字节重现证书：

```sh
python3 scripts/check_regeneration.py
```

该检查使用临时副本，结束后自动清理；实际记录见 `logs/regeneration-check.txt`。

证书生成器也一并提供：`scripts/generate_candidates.py`、
`scripts/generate_commutation.py`、`generate_rank_certificates.py` 和 `tools/generate_distance.py`。
无需重新生成即可验证现有源码。重生成会覆盖相应文件；建议在副本中操作，
比较差异后重新构建，而非把生成器的成功退出当作证明完成。

## 4. 交付证据和完整性

独立审计于 2026-10-17 04:57:48 UTC 完成。两阶段串行编译和检查累计约 1,241 秒；
该时间仅记录本次环境，不能视为其他机器上的运行时保证。
审计源码清单 SHA-256 为
`e39ba2ea1d454b80e810fbf6cfa2986590400c3aa931720f1b0ff83a9952167a`。

- `audit/REVIEW.md`：独立语义及信任边界审查。
- `audit/final-result.json`：最终干净构建步骤、退出码、耗时、工具链及源码未变化检查。
- `audit/final-build.log`：最终构建及公理输出的实际日志。
- `audit/source-manifest.json`：最终独立构建所使用的源码哈希。
- `audit/scan_proof_sources.py` 与 `audit/source_scan.json`：去掉注释及字符串后检查证明源码；静态扫描只是最终内核构建及公理审计的补充。
- `audit/literal_binding.json`、`audit/independent_candidate_audit.json`：外部绑定与独立计算结果。
- `audit/AuditSanity.lean`：生成空间、相关行、Y 重量和相位误判等语义回归例。
- `logs/final-build.txt`、`logs/final-axioms.txt`、`logs/source-trust-check.txt` 和 `logs/final-proof-source-sha256.json`：开发构建的最终通过记录及冻结源码哈希。
- `logs/` 中其他文件：开发过程中保留的真实命令输出；历史局部日志不取代最终干净构建结果。
- `SOURCE_MANIFEST.json`：交付包每个普通文件的 SHA-256 和字节数（不含清单本身及 `SHA256SUMS`）。
- `SHA256SUMS`：包含上述清单在内的文件哈希，可用 `sha256sum -c SHA256SUMS` 验证。

压缩包不包含本地私人笔记、原研究仓库、工具链二进制、缓存或临时审计副本。
打包验证还会解析全部 JSON，核对每个归档文件的哈希并检查 ZIP CRC。
