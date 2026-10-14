# MyLean

数学の各種定理・補題をLean 4で形式化する個人研究・開発リポジトリ。

---

## ディレクトリ構成

```text
MyLean/
├── Common/                 # 分野横断で利用する共通の記法・マクロ・補助定理
│   ├── Basic.lean
│   └── ...
├── Algebra/                # 代数学 (Algebra)
├── Analysis/               # 解析学 (Analysis)
├── Geometry/               # 幾何学 (Geometry)
├── NumberTheory/           # 数論 (NumberTheory)
├── Combinatorics/          # 組合せ論・離散数学 (Combinatorics)
├── Topology/               # 位相空間論 (Topology)
├── LinearAlgebra/          # 線形代数 (LinearAlgebra)
├── Probability/            # 確率論・測度論 (Probability)
├── SetTheory/              # 集合論・基礎論 (SetTheory)
├── CategoryTheory/         # 圏論 (CategoryTheory)
└── Exercises/              # 大学などの講義課題・演習・テスト
    └── <SubjectName>/      # 科目名 (例: LinearAlgebra1)
        └── <Assignment>/   # 課題名 (例: HW01, Midterm)

templates/
├── proof/                  # [一般定理用] 新しい証明を作成するためのテンプレート
│   ├── Statement.lean      # 主張・前提定義 (初期は sorry)
│   ├── Proof.lean          # 証明本体
│   └── README.md           # 定理の概要・文献メモ
└── exercise/               # [大学演習用] 課題・テストを作成するためのテンプレート
    ├── Statement.lean      # 問題用紙 (問1, 問2...の主張)
    ├── Proof.lean          # 解答用紙 (証明本体)
    └── README.md           # 課題情報 (出題日・提出期限など)
```

---

## 開発ワークフロー

本プロジェクトでは `main` ブランチを保護し、作業ブランチからPull Request経由で反映します。

### 1. 新しい作業ブランチの作成

```sh
git checkout main
git pull
git checkout -b feat/algebra-lagrange
```

### 2. テンプレートから証明ディレクトリをコピー

例として、代数学(Algebra)に `LagrangeTheorem` を追加する場合:

```sh
cp -r templates/proof MyLean/Algebra/LagrangeTheorem
```

### 3. モジュール名と内容の編集

コピーしたファイルの namespace を変更して作業します。

- `MyLean/Algebra/LagrangeTheorem/Statement.lean`: 定理のステートメントを記述
- `MyLean/Algebra/LagrangeTheorem/Proof.lean`: 形式証明を記述
- `MyLean/Algebra/LagrangeTheorem/README.md`: 文献・背景のメモを記録

### 4. ハブモジュールへの登録

証明が完成したら、該当分野のハブモジュール(例: `MyLean/Algebra.lean`)にインポートを追記します。

```lean
import MyLean.Algebra.LagrangeTheorem.Proof
```

### 5. ビルド検証とPull Request

```sh
lake build
```

ビルドが成功したらコミットし、Pull Requestを作成して `main` ブランチへマージします。

---

## 大学の課題・演習 (Exercises) の追加手順

大学の講義課題やテスト対策は、`templates/exercise` を利用して科目ごとに管理します。

```sh
# 1. テンプレートをコピー (例: 線形代数1の第1回課題)
cp -r templates/exercise MyLean/Exercises/LinearAlgebra1/HW01

# 2. 編集
# Statement.lean に問題文(問1, 問2...)を記述
# Proof.lean に各問の解答・証明を記述
# README.md に出題日や提出期限をメモ

# 3. 完成したら MyLean/Exercises.lean に import を追記
# import MyLean.Exercises.LinearAlgebra1.HW01.Proof
```
