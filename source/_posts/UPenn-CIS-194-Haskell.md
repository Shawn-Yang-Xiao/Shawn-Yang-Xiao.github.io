---
title: UPenn CIS 194 Haskell
toc: true
date: 2023-04-13 14:17:32
tags:
categories:
---


# Haskell

with [UPenn CIS 194: Introduction to Haskell (Spring 2013)](https://www.cis.upenn.edu/~cis1940/spring13/)

and with Algebra of Programming (Richard Bird & Oege de Moor)

## 基本语法

- 操作符
  - `==` 等于
  -  `/=` 不等于
  -  `++` 两个列表相加
  - `：`  向列表前加入一个元素
  - `--` 或 `{- ... -}` 注释
  - `$`  apply 分隔函数和参数（类似于括号）
  - `where` 在alternatives中用于定义重复使用的变量

<!--more-->

- 列表 `list`
  - `[ .. ]`
  - 自动填充，如`[1..10]`
  - 列表中的元素必须是相同类型
  - `head`首个元素
  - `tail`除首个元素之外的部分（作为一个列表返回）
  - `null List` 检查List中是否有元素 `null:: [a] -> Bool`
  - `reverse List` 将List反转
  - `take num List` 返回List前num个元素（作为一个列表）
  - `drop num List` 删除List中前num个元素，并返回操作后的列表（如果num大于等于列表长度则返回空列表）
  - `min List` 返回列表中最小值
  - `sum List` 返回列表元素之和
  - `product` 返回列表元素之积
  - `listName !! index` 下标运算符
  - `ele  ·elem·   List` 判断元素ele是否在列表List中，`·notElem·`相反
  - `cycle List / repeat Ele` 利用列表List或者元素Ele生成无线列表
  - `replicate num Ele` 得到Ele重复num次构成的列表
  - `lines :: String → [String]`  将一段内容分行，可以用`map func  . lines` 表示对每行施加函数func
- `Tuple (ele1, ele2, ...)`
  - fixed-size collection of values
  - each value can have a different type
- 列举类型的元素 `data DataType = xxx ; | xxx ; | xxx; ... ; deriving (Eq,Show)`
- 说明
  - `:info (operator)`
  - `:type ele` 判断元素的类型
  - `:set prompt "ghci>"` 修改提示符设置
- 函数
  - `funcname args = ...`
  - 函数首字母不能大写
  - `:| filename` 装载中的函数以供使用
  - 本质上，Haskell的函数都只有一个参数，所有多个参数的函数都是Curry函数，先返回取第一个数为参数的函数，然后再以第二个数为参数调用它
  - 用不全的参数调用函数可以创造新的函数
- Haskell高阶函数
- Type constructor
  - `data TypeName = Constructor ... ; deriving (Show)`
  - newtype TypeName = Constructor Field  – – different from data keyword, newtype can only have one constructor and exactly one field.
- if-then-else 中 else 不可忽略


## Haskell模块
- 加载模块
  - `import moduleName` (e.g. `Data.List`)
  - `:m modName1 modName2 modName3`
  - 加载模块中的函数 `import modName (funcName1, funcName2`
  - 除某个函数以外加载 `import modName hiding (funcName)`
  - 防止重名，要求全名指定 `import qualified modName1`
  - 库重命名 `import quantified modName as varName`
- 用Hoogle检索函数  https://hoogle.haskell.org/
- 常用模块
  - Prelude
    - Prelude is a module with a bunch of standard definitions that gets implicitely imported into every Haskell program.
    - `data Maybe a = Nothing | Just a`  : A useful polymorphic type, either contains a value of type a (wrapped in the Just constructor), or it is nothing (representing some sort of failure or error)
  - Data.List
    - `intersperce ele List` 将元素ele置于List每两个元素之间
    - `intercalate List1 List2` 将List1置于List2每两个元素之间
    - `transpose` 视列表的列表为矩阵进行转置操作
    - `any`/`or` `boolFunc List` 检查元素符合条件
    - `takeWhile boolFunc List` 遇到false停止 （类似函数有`span`, `break`）
    - `delete ele List` 删掉该List中首次出现的这一元素
    - `List1 \\ List2 ` 差集操作List1-List2
    - `List1 ·union· List2` 并集（遍历List2，若某元素不属于List1，则追加到List1后）
    - `List1 ·intersection· List2` 交集
  - Data.Char
    - 字符串的本质就是一组字符的List，所以往往会在`filter`或是`map`字符串时用到
    - `generalCategory`函数返回值是情况的枚举（参考`Ordering LT, GT, EQ`）
- Haskell 输入与输出
  - `main = putStrLn "hello, world"`
  - `putStrLn`型态为`IO()`，`putStr()`不打印换行，`putStr()`由`putChar()`递归定义得到
    `putStr(x:xs) = do ; putChar x ; putStr xs`
  - 一个I/O action会在绑定到`main`并执行程序的时候被触发
  - 用`do`表示法将所有的I/O action绑成一个
  - 读出内容 `var<-getLine`
  - 注意区分：`oper=getLine`只是为`getLine`取了一个别名
  - `when`在Control.Monad中，必须import才能得到
    - 接受boolean值跟I/O action，如果True，就回传所给的I/O action，否则回传`return()`
  - `sequence`接受一串I/O action，并回传会依序执行他们的I/O action（ `sequence :: [IO a] -> IO[a]` ）
  - `forever`在Control.Monad中，回传一个永远作同一件事的I/O action
  - 文件流`getContents`标准输入读取至EOF。惰性I/O，并不会马上读取所有输入
  - 读取文件 `handle <- openFile fileName ReadMode ; contents <- hGetContents handle ; ... ; hClose handle ; (openFile :: FilePath -> IOMode -> IO Handle)`
  - 其中，`openFile`，`ReadMode`，`hGetContents`，`hClose`；`type FilePath = String`, `data IOMode = ReadMode | WriteMode | AppendMode | ReadWriteMode`
  - 或者用`contents <- readFile fileName` 读取文件，无需考虑句柄的关闭
  - Map implementation:
    ```Haskell
    map :: (a, b) → [a] → [b]
    map _ [] = []
    map f (x:xs) = f x : map f xs
    ```
  - Filter implementation:
    ```Haskell
    filter :: (a → Bool) → [a] → [a]
    filter _ [ ] = [ ]
    filter p (x:xs)
       | p x = x : filter xs
       | otherwise = filter xs
    ```
  - Fold implementation. e.g. `fold (+) 0 [1,2,3,4,5] => (1+(2+(3+(4+(5+0)))))`
    ```Haskell
    foldr :: (a → b → b) → b → [a] → b
    foldr _ z [ ] = z
    foldr f z (x:xs) = f x (foldr f z xs)
    ```



## UPenn CIS 194 2013

### Week 2: Type Construct

- Enumeration types:
  - `data TypeName = ele1 ; | ele2 ; … ; deriving (Show, Eq, … )`
  - `data AlgDataType = Constr1 Type11 Type12; | Constr2 Type 21 ; … ; deriving (Show, Eq , …)`
  - `func :: type1 → type2 ; func ele1 = ele2 ; func ele3 = ele4 ; … ; func _ = rest`


### Week 4: Higher-order programming and type inference
- Anonymous functions (lambda abstraction)
  - Here is an example
    ```Haskell
    greaterThan100 [1, 9, 349, 6, 907] = [349, 907]
    greaterThan100 :: [Integer] → [Integer]
    greaterThan100 xs = filter (\x → x > 100) xs
    Or equivalent: greaterThan199 xs = filter (>100) xs
    ```
  - `\` is supposed to be as lambda, function `\x -> x > 100` outputs whether x is greater than 100
  - `(>100)` is an operator section: `?y` is equivalent to `\x -> x ? y`, and `y?` Is equivalent to `\x -> y ? x`
- Function composition `(f.g)`
  - useful in writing concise, elegant code
- Currying and partial application
  - `\x y z ->` is syntax for `\x -> (\y -> (\z -> ... ))`
- Wholemeal programming
  - ```Haskell
    foobar :: [Integer] → Integer
    foobar [] = 0
    foobar (x:xs)
      | x > 3 = (7*x+2) + foobar xs
      | otherwise = foobar xs

    foobar’ :: [Integer] → Integer
    foobar’ = sum . map (\x -> 7*x + 2) . filter (>3)
    ```
- Avoid the problem of doing too much at once and working at too low of a level.
- This defines foobar' as a "pipeline" of three functions. First filter, then apply to every element, eventually sum them up.
- Folds
  - ```Haskell
    fold :: b → (a → b → b) → [a] → b
    fold z f []  = z
    fold z f (x:xs) = f x (fold z f xs)
    ```
  - fold is already provided in the standard Prelude, under the name of `foldr :: (a→b→b) → a → [a] → b`
  -	There is also `foldl`, which folds from the left (use `foldl'` from Data.List is more efficient)

### Week 5: More Polymorphism and Type Classes

- Parametricity
  - `a -> a -> a` is a promise that `a` function with this type will work no matter what type the caller chooses, otherwise specify the type
- Type classes
  - Num, Eq, Ord and Show are type classes, and we say that `(==)`, `(<)`, `(+)` are "type-class polymorphic".
  - `deriving (Eq, Ord, Show)` Tell GHC to automatically derive instances of the `Eq`, `Ord`, and `Show` type classes for our data type.
- Standard type classes
  - Ord: totally ordered, any two elements can be compared to see which is less than the other.
  - Num: numeric types, support things like addition, subtraction, and multiplication.
  - Show: defines the method Show, which is used to convert values into Strings
  - Read: the dual of Show
  - Integal: represents whole number types such as Int and Integer


### Week 6: Lazy Evaluation

- Strict evaluation
  - Opposite to lazy evaluation, function arguments are completely evaluated before passing them to the function.
- Consequences
  - Purity
  - To the recursion function, whether the list should be recursed before processed, or computed first before unwinding.
  - For example, foldl’ requires the second argument to be evaluated before it proceeds, so a large thunk never builds up (compared with function foldl).
- Infinite data structures
  - Lazy evaluation means that we can work with inifinite data structures. Defining an infinite data structure actually only creates a thunk, which we can think of as a “seed”, out of which the entire data structure can potentially grow.
- Dynamic programming
  - One must take great care to fill in entries of a dynamic programming table in the proper order, so that its dependencies have already been computed. If we get the order wrong, we gor bogus results.



### Week 8: I/O

- `main` itself is an I/O action with type IO()
- `do` defines a sequence of actions
- Combining IO
  - `(>>) :: IO a -> IO b -> IO b` ––running two input computation in sequence
  
