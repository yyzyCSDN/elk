# `switch!` 穷尽性匹配表达式

## 为什么需要 `switch!`

普通 `switch` 表达式在没有任何分支命中时会得到 `nil`，因此它的结果类型总是隐含一个
`nil`。在协议消息分派这类场景中，我们希望编译器保证每个可能的输入都有分支处理，
并在漏写分支时直接报错，而不是把错误留到运行时。

`switch!`（读作 *strict switch*）就是带编译期穷尽性证明的 `switch`：

- 所有可能的值都被纯模式分支或 `else` 分支覆盖时，编译通过；
- 证明通过后，结果类型中**不再注入 `nil`**；
- 无法证明时编译失败，并给出一个具体的漏匹配值作为诊断。

## 语法

`switch!` 与普通 `switch` 语法一致，只是关键字后紧跟一个 `!`（中间不能有空白）：

```elk
def classify(a: 1 | 2 | 3): Symbol
  switch! a
  case 1 then :one
  case 2 then :two
  case 3 then :three
  end
end
```

注意 `switch !foo`（带空格）仍然表示对表达式 `!foo` 做普通 `switch`，
只有相邻的 `switch!` 才是穷尽性匹配。

## 可被证明的类型域

穷尽性分析只信任不执行用户代码的“纯”信息，支持以下类型的任意嵌套：

- `nil`、`Bool`；
- `Int`、`String`、`Symbol` 的有限字面量联合；
- 原生 `ArrayList` 与 `ArrayTuple`（任意层级嵌套）；
- 以上类型组成的联合类型与可空类型（`T?`）。

可靠（纯）模式包括：

| 模式 | 示例 | 说明 |
| --- | --- | --- |
| 绑定 | `x`、`_` | 覆盖该位置的全部值 |
| 字面量 | `nil`、`true`、`3`、`"a"`、`:foo` | 单个字面量值，含负数字面量 `-1` |
| 列表/元组 | `[1, x]`、`%[1, *r]` | 长度与每个位置联合约束 |
| 任意位置的单个 rest | `[first, *middle, last]` | 覆盖任意长度，rest 可在任意位置 |
| `as` | `(1 || 2) as x` | 约束等价于内部模式，同时绑定 |
| 可空 | `s?` | 内部模式并上 `nil` |
| `must` | `must` | 除 `nil` 外的全部值 |
| `||` / `&&` | `"a" || "b"`、`x && 1` | 模式空间的并与交 |

列表长度不是靠固定枚举处理的：分析同时推理“长度”和“各位置约束”，
开放形状（带 rest）覆盖所有超过语法固定数量的长度，嵌套深度也没有限制。

## 漏匹配诊断

当分支不全且全部为纯模式时，编译器会给出一个符合类型的具体漏匹配值，例如：

```elk
var a: 1 | 2 | 3 = 1
switch! a
case 1 then :a
case 2 then :b
end
# FAIL: non-exhaustive `switch!` expression, no branch matches the value 3
```

列表场景同样会给出最短的具体见证值：

```elk
var a: ArrayList[1 | 2] = []
switch! a
case [1, *r] then :one
end
# FAIL: ... no branch matches the value []
```

被前面分支完全覆盖的纯分支会产生不可达警告：

```elk
switch! a
case true then :t
case false then :f
case true then :x  # WARN: this branch is unreachable ...
end
```

## 动态（不纯）模式的失效规则

下面这些模式会执行用户代码，不能作为可靠的覆盖证明：

- 动态值与相等/关系比较：`== x`、`> 5`、常量模式；
- 正则：`%/pattern/`；
- 对象 getter：`String(length: 1)`、推断对象模式 `@{ ... }`；
- 区间、map/record/set、宏调用等。

它们仍然可以在 `switch!` 中正常使用（运行时语义与普通 `switch` 完全相同），
但只要出现且没有 `else` 或后续纯分支补全覆盖，编译器就会给出明确的
“无法证明穷尽性”诊断，而**不会编造一个见证值**：

```elk
var a: String = "x"
switch! a
case %/x/ then :r
case "y" then :y
end
# FAIL: cannot prove exhaustiveness of this `switch!` expression:
#       a branch uses a dynamic pattern that may invoke user code and
#       mutate the matched value; add a pure catch-all branch or an `else` branch
```

动态模式可能修改匹配值引用的可变结构，因此经过动态分支后，所有依赖可变内容
（列表长度、元素等）的覆盖事实都会失效；只有 `nil`、`Bool`、字面量这类
不可变标量单例事实保留。其后的纯分支可以重新完成证明：

```elk
switch! a
case %/x/ then :r       # 动态分支，覆盖事实重置（标量事实保留）
case "x" then :x
case "y" then :y        # 纯分支重新证明穷尽
end
```

任何时候都可以用 `else` 兜底：

```elk
switch! a
case %/x/ then :r
else :fallback
end
```

## 结果类型不含 `nil`

一旦穷尽性得到证明（纯分支全覆盖，或存在 `else`），表达式的结果类型就是各分支
结果类型的联合，不会因为“可能落空”而加入 `nil`：

```elk
var a: 1 | 2 = 1
var b: Symbol = switch! a
  case 1 then :one
  case 2 then :two
  end   # 类型为 :one | :two，可以赋给非可空的 Symbol
```

## 运行时保证

`switch!` 复用普通 `switch` 的同一套编译与 VM 执行路径，因此：

- 被匹配表达式只求值一次；
- 分支按书写顺序短路匹配，首个命中的分支生效；
- 模式绑定、rest 绑定、副作用时机与普通 `switch` 完全一致；
- 字节码 VM 与 Go 原生编译器两个入口行为一致。

穷尽性证明完全在编译期进行，不会执行任何用户代码，也不会引入额外的运行时开销。
