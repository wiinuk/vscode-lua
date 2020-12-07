# 構文
```abnf
escape = "amp" | "quot" | "apos" | "lt" | "gt" | [0-9]+ | "#" [0-9a-fA-F]+
comments0 = ( [^@\n&] | "&" escape ";" )*

tag =
  ; name の後にタグ名に依存した構文が続く
  / "@" name …
  ; 不明なタグのスキップルール
  / "@" name comments0

document = comments0 tag*

longDocument = "--[" "="{n} "[" trivia* "]" "="{n} "]"
lineDocument = "---" document ("\n" | $)
trivia =
  | whiteSpace
  | (lineDocument / lineComment)
  | longDocument
```

## --[[---@tag]] 形式のドキュメントコメント
### --[[---@tag]] 形式のドキュメントコメントの例
```lua
local x = --[[---@type string]](42)
```

# @type
## @type の構文
```abnf
fieldKey =
  | "true"
  | "false"
  | ("-" | "+")? number
  | name
  | string

field = fieldKey ":" functionType
fieldSep = "," | ";"
interfaceType = "{" field (fieldSep field)* fieldSep? "}"
constraints = interfaceType

parameter =
  / name ":" functionType
  / functionType

; name は複型変数 `T...`
; type は全要素制約 `T...: string`
; `...` は `T...` の略記
; 同じスコープに現れる `...` は全て同じ複型変数を示す
; 複型変数名が明示的に指定された `T...` 形式は `fun(T...): (U...)` のように使われる。
; 似たように見える `fun(...): (...)` は `fun(T...): (T...)` の略記。
varParameter = name? "..." (":" type)?

parameters1 =
  | varParameter
  | parameter ("," parameter)* ("," varParameter)?

parameters0 = "(" parameters1? ")"

primitiveType =
  ; スコープにない名前 `void` は空型 `()` として扱う
  ; スコープにない名前 `any`, `_` は自動的に型変数になる。同じ名前は違う型変数を表す
  ; スコープにない、大文字の 'T' から始まり2文字目が小文字でない名前 ( `T`, `TResult`, `T2`, `TYPE` など ) は自動的に型変数になる。同じ名前は同じ型変数を表す
  ; スコープにない1文字の名前 `U`, `a` などは自動的に型変数になる。同じ名前は同じ型変数を表す
  ; スコープにない `self` は文脈に関連づけられた型を表す
  ; スコープにない他の名前はエラー
  ; 型変数のアリティは常に 0 とみなす。例えば `a` が型変数のとき `a<string>` はエラー
  | name

  ; 空型
  | "(" ")"
  ; 複型変数
  | name? "..." constrainedType?
  ; 1要素の複型
  | "(" parameter "," ")"

  ; ジェネリック型
  ; アリティはチェックされるので、グローバルに定義済みの `string` に対して `string<T>` はエラー
  | name "<" functionType ("," functionType)* ">"

  | interfaceType

  | "(" multiType ")"

arrayType =
  | primitiveType

  ; `table<number, type>` の略記
  | arrayType "[" "]"

constrainedType =
  | arrayType

  ; 制約付き型 `T: { x: number }`
  ; type が `{ name: string, age: number }: { age: number }` のように型変数でないなら、一致するかチェックする
  | constrainedType ":" constraints

functionType =
  | constrainedType

  ; 型 `fun` とは別
  | "fun" parameters0 ":" functionType

multiType =
  | functionType
  | parameter "," varParameter
  | parameter ("," parameter)+ ("," varParameter)?

type = functionType

typeTag = "@type" type
```

### @type を認識できる場所
- 式を囲む括弧 `(` `)` の左

  式の型を無条件に注釈された型として扱う。型安全ではない

  例:
  ```lua
  local x = --[[---@type string]](42)
  -- Ok: x: string
  ```

## @type の意味

### 型変数のスコープ
スコープにない型変数 `T` が指定された場合、
最も近い `---@generic` タグがつけられる親要素をスコープとする。
`---@generic` タグがつけられる親要素がない場合、チャンクをスコープとする

```lua
---@type T
local x1 = 0 -- Ok: T は number に置き換えられる

---@type T
local x2 = "" -- Error: 型の不一致

local function f()

  ---@type T
  local x3 = "" -- Ok: x1 の T と x2 の T は別の型

  ---@type U
  local y1 = true -- Ok: T は boolean に置き換えられる

  local function g()

    ---@type U
    local y2 = "" -- Ok: y1 の U と y2 の U は別の型
  end
end

for _ = 0..0 do
  ---@type T
  local x4 = "" -- Error: 型の不一致、for 式はスコープを作らない
end
```

### 複型変数のスコープ
```lua
-- 名前付き複型変数 `V...` のスコープは型変数のスコープと同じ
```

### 名前なし複型変数の自動名付け
同じ関数型内の名前なし複型変数は同じ複型変数になる
```lua
---@type fun(fun(...): (...), fun(...): (...), ...): (...)
-- は以下と同じ意味
---@type fun(fun(T...): (T...), fun(U...): (U...), V...): (V...)
```

### 明示的に指定された型引数のスコープ
@generic で明示的に指定された型引数は、親 @type の中と、子 @generic からしか見えない
```lua
-- 型引数を明示的に指定した場合
local id = --[[---@generic a @type fun(a): a]](42)
local x1 = id"a" -- Ok: x1: string
local x2 = id(7) -- Ok: x2: number

-- 自動型変数の場合
local id = --[[---@type fun(T): T]](42)
local x1 = id"a" -- Ok: x1: string
local x2 = id(7) -- Error: number と string の不一致
```

# @global
## @global の構文
```abnf
globalTag = "@global" name type
```
### @global を認識できる場所
- 空ブロックの中
  ```lua
  ---@global n t
  ```
  ```lua
  do
    ---@global n t
  end
  ```
- 文の前後
  ```lua
  ---@global n t
  local function f() end
  ---@global n t
  f()
  ---@global n t
  ```

## @global の意味
```lua
---@global MyNaN number
local n = MyNaN -- Ok：`MyNaN` が使える

local n = MyInf -- Error：`MyInf` は宣言されていない

local function f()
  ---@global MyInf number
  local n = MyInf -- Ok：`MyInf` が使える
end

local n = MyInf -- Ok：ローカルで宣言した `MyInf` がスコープを超えて使える

---@global MyNaN number
-- Ok：型が一致していれば再び宣言できる

---@global MyNaN string
-- Error：型が一致していない


-- グローバル変数宣言の型変数スコープはそのタグのみ
---@global x fun(T): ()
---@global y fun(T): ()

x(10)  -- Ok
x("a") -- Ok
y(10)  -- Ok
y("a") -- Ok
```

### 追加的グローバル環境と伝播
- モジュール M の追加的グローバル環境とは以下を合わせたもの
  - M で宣言や代入によって追加されたグローバル環境
  - M の親モジュールの追加的グローバル環境
- 初期グローバル環境は含まない

```lua
-- lib1.lua ---------------------------
---@global Lib1State string
Lib1State = "ready"

-- lib2.lua ---------------------------
---@global Lib2Counter number
Lib2Counter = 42

-- lib3.lua ---------------------------
local s = Lib1State -- Error：`Lib1State` は宣言されていない
require "lib1"

local s = Lib1State -- Ok：`lib1.lua` で宣言されている `Lib1State` が使える

local function f()
  -- lib2 に追加的グローバル変数があるなら警告
  require "lib2" -- Warning：lib2 の追加的グローバル変数が未確定になる事を報告し、`require` をソースの一番上に移すことを提案する
  local s = Lib2Counter -- Ok：`lib2.lua` で宣言されている `Lib2Counter` が使える
end

local s = Lib2Counter -- Ok：`lib2.lua` で宣言されている `Lib2Counter` が使える

-- main.lua ---------------------------
require "lib3" -- 先祖に `lib1` と `lib2` を含む

local s = Lib1State -- Ok：`lib1.lua` で宣言されている
local s = Lib2Counter -- Ok：`lib2.lua` で宣言されている
```

### @global 同士の衝突
- 変数宣言時の衝突エラーは即報告する
- 親モジュールによって導入された変数の衝突のエラーは、変数の使用時に報告する

```lua
-- lib1.lua ---------------------------
---@global Id string
Id = "abc"
---@global Lucky boolean
Lucky = true

-- lib2.lua ---------------------------
---@global Id number
Id = 123
---@global Lucky boolean
Lucky = true

-- main.lua ---------------------------
require "lib1"
require "lib2" -- ここではエラーは出ない

-- 衝突した変数の使用時にエラー
local x = Id -- Error：`lib1.lua(0,3)` と `lib2.lua(0,3)` で宣言されているグローバル変数 `Id` の型の不一致

local x = Lucky -- Ok：エラーは出ない
```

### @global と local の衝突
```lua
local function f()
  local X = 10
  ---@global X string
  -- Ok：ローカル変数と同じ名前のグローバル変数を宣言できる

  local x1 = X -- Ok：ただし `X` はローカル変数を指しているので `x1` の型は `number`
end

local x2 = X -- Ok：宣言されたグローバル変数 `X` を使える。`x2` の型は `string`
```

# @class

## @class の構文
```abnf
interfaceTag = "@class" name (":" type)?
propertyTag = "@field" ("public" | "protected" | "private")? fieldKey type
```

### @class を認識できる場所
- @global と同じ

## @class の例
```lua
---@class set : table<K, nil>

---@class Vector2
---@field x T
---@field y T

---@class Vector3 : Vector2<T>
---@field z T
```

## @class の意味
- 「親型」と「指定されたキーと値の型を持つインターフェース型」の交差型を、別名として定義する
  - `newTypeName = (?self & parentType & { field1: fieldType1 } & { field2: fieldType2 } & …)`
- 前に `@class` のない `@field` は無視される
- 型名が見える範囲
  - `@class` タグの中
  - 子の `@field` タグの中
  - `@class` の定義が終わった後
    - グローバルに見える
- 基本型と同名の型は宣言できない
- 型引数の見える範囲は最後の `@class` または `@field` タグまで
- visibility は無視される
- 同じ名前の型の再定義は型が一致していれば可能。一致していなければエラー
- 型表記中の self は、定義中の型名に関連付けられる

```lua
---@field f number
-- Warning: `@class` が必要。このタグは無視される

---@class Vec2
---@field x number
local a = 123
---@field y number
-- Warning: `@class` が必要。このタグは無視される ( Vec2 = { x: number } )

---@class Id : string
-- Ok: `Id` は `string` の別名

local function f()
  ---@class Null : nil
  -- Ok
end

---@global null Null
-- Ok: 型 `Null` は見える

---@class string : { chars: number[] }
-- Error: 基本型 'string' と同名の型の宣言

---@class ParentTypeMismatch : number
---@field f1 string
-- Error: `number` と `{ f1: string }` の不一致

---@class FieldTypeMismatch : { f1: number }
---@field f1 string
-- Error: `number` と `string` の不一致

---@class Vector2
---@field x T
---@field y T

---@class Vector4 : Vector2<T>
---@field z T
---@field w T

---@global N4 Vector4<number>
local x = N4.x -- Ok x: number
local w = N4.w -- Ok w: number

---@global S4 Vector4<string>
local x = S4.x -- Ok: x: string
local w = S4.w -- Ok: w: string

---@class Bigint : string
---@class Bigint : Id
-- Ok: `string` と `Id` は一致している

---@class Bigint : number
-- Error: `string` と `number` は一致していない

---@class Shape
---@field contains fun(Shape, x: number, y: number): boolean
---@field area fun(self): number

---@class Polygon : Shape
---@field vertexCount fun(self): number
---@field vertex fun(self, i: number): (x: number, y: number)
```

# @generic
## @generic の構文
```abnf
typeParameter =
  | name (":" constraints)?
  | name "..." constrainedType?

genericTag = "@generic" typeParameter ("," typeParameter)*
```

### @generic を認識できる場所
- `@class` の前
  ```lua
  ---@generic Contents
  ---@class Box
  ---@field contents Contents
  ```

- `@field` の前
  ```lua
  ---@class ArrayUtils
  ---@generic T
  ---@field create fun(...T): T[]
  ```

- `@type` の前
  ```lua
  local id = --[[---@generic T @type fun(T): T]](42)
  ```

- `@global` の前
  ```lua
  ---@generic Args...
  ---@global id fun(Args...): Args...
  ```

## @generic の意味
- 親要素と型制約の中でのみ見える、指定された名前の型引数を使えるようにする
- 親要素
  - `@class`
  - `@field`
  - `@type`
  - `@global`

- 親要素の前の複数の `@generic` タグが認識される
- 親要素を持たない `@generic` は無視される

- 型引数は外側の同じ名前の型を隠す
- 基本型と同じ名前を持つ型引数を宣言できる
- 重複した型引数名の種類と制約は単一化され、エラーがあったら報告される
- 複型引数と複型でない型引数を同時に同じ名前で宣言することはできない
- 複型引数は必ず名前の後に "..." をつける必要がある
```lua
---@generic number
---@class Vector2
---@field x number
---@field y number

---@global S2 Vector2<string>
local s2x = S2.x -- Ok: s2x: string

do
  ---@generic X
  -- Warning: このタグは無視される
end

---@generic V: { x: N }
---@generic V: { y: N }
---@generic N
---@class Segment2
---@field p1: V
---@field p2: V

---@global Seg Segment2<{ x: number, y: number, z: number }, number>
local p1z = Seg.p1.z -- Ok: p1z: number

---@generic T: { x: string }
---@generic T: { x: number }
---@class ConstraintMismatch
-- Error: string と number が一致しない


---@class Utils
---@generic T
---@field createArray fun(...T): T[]
---@generic T
---@field id fun(T): T

---@global Utils Utils
local xs1 = Utils.createArray(123, 456) -- Ok: xs1: number[]
local xs2 = Utils.createArray("abc", "dfg") -- Ok: xs2: string[]
local x1 = Utils.id(10) -- Ok: x1: number
local x2 = Utils.id("abc") -- Ok: x2: string

---@generic A
---@generic A...
---@class TypeParameterKindMismatch
-- Error: A の種類が一致しない

---@generic V...
---@class TypeVariableKindMismatch
---@field ignore fun(V): ()
-- Error: ここに複型は置けない
```
