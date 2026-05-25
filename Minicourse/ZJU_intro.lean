import Mathlib

/-
# 目标

1. 拿到lean项目，能跑
2. 简单回顾怎么看lean代码
3. 跑完知道哪里有问题
-/

/-! # Lean项目的基本管理

**拿到一个lean项目，怎么运行**

1. 项目根目录里必须有：
  · lean-toolchain
  · lakefile.toml

2. 看：
  · √ lake-manifest.json ->
      `lake exe cache get`   && `lake build`
       ↑ 获取mathlib的编译缓存     ↑ 编译本项目

  · ⨯ lake-manifest.json ->
      在lakefile.toml里mathlib的require下面加`rev = "v4.29.1"`
      `lake --keep-toolchain exe cache get` && `lake build`
            ↑ lean会激进地想要更新，但lean的更新是不向下兼容的
              在复杂项目上会产生大量报错

**创建指定版本的lean项目**

`lake +leanprover/lean4:v4.28.0 new baseline math`

**切换lean版本**

1. `rm -rf .lake` 删除已有的所有缓存
2. `rm lake-manifest.json`
3. 编辑`lean-toolchain`
4. 回到之前的步骤

**共享manifest和缓存**

网络不好下载不了缓存/拼尽全力无法战胜lake的自动升级
  ↓
创建同一版本的lean项目/clone已有的同一版本的lean项目
  ↓
把`.lake`文件夹和`lake-manifest.json`直接拷过来

-/
