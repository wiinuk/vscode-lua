---@_NoImplicitRequire

-- Basic Functions -----------------------------------

---@global assert fun(v: T, ...): (v: T, ...)

-- TODO:
--@global collectgarbage ((fun(opt: "stop"): ()) | (fun(opt: "restart"): ()) | (fun(opt: "collect"): ()) | (fun(opt: "count"): number) | (fun(opt: "step", size: number): boolean) | (fun(opt: "steppause", pause: number): ()) | (fun(opt: "setstepmul", stepMultiplier: number)))
---@global collectgarbage fun(opt: string, ...number): TResult...

-- TODO:
--@_Feature dofile
---@global dofile fun(filename: string): R...

-- TODO:
--@global error fun(message: string [, level: number]): ...
---@global error fun(message: string, ...number): TAny...

-- TODO:
--@_Feature global
---@global _G nil

-- TODO:
--@global getfenv fun(f: (fun(T...): R...) | number): E
---@global getfenv fun(f: F): E

---@global getmetatable fun(object: T): M

-- TODO:
--@global ipairs fun(t: T[]): (iter: fun(t: T[], i: number): (() | (i: number, v: T)), t: T[], i: number)
---@global ipairs fun(t: T[]): (iter: fun(t: T[], i: number): (i: number, v: T), t: T[], i: number)

-- TODO:
--@global load fun(func: fun(): (string | ()) [, chunkname]): ((chunk: fun(...): R...) | (nil, errorMessage: string))
---@global load fun(func: (fun(): string), ...string): (chunk: fun(TArgs...): TResult...)

-- TODO:
--@_Feature loadfile
--@global loadfile fun([filename: string]): ((chunk: fun(...): R...) | (nil, errorMessage: string))
---@global loadfile fun(...string): R...

-- TODO:
--@_Feature loadstring
--@global loadstring fun(string: string [, chunkname: string]): ((chunk: fun(...): R...) | (nil, errorMessage: string))
---@global loadstring fun(string: string, ...string): R...

-- TODO:
--@global next fun(table: table<K, V> [, index: K]): ((nextIndex: K, currentValue: V) | ())
---@global next fun(table: table<K, V> ...K): (nextIndex: K, currentValue: V)

-- TODO:
--@global pairs fun(t: table<K, V>): (next: (fun(table: table<K, V> [, index: K]): ((nextIndex: K, currentValue: V) | ())), t: table<K, V>, nil)
---@global pairs fun(t: table<K, V>): (next: (fun(table: table<K, V> ...K): (nextIndex: K, currentValue: V)), t: table<K, V>, nil)

-- TODO:
--@global pcall fun(f: (fun(T...): R...), T...): ((true, R...) | (false, errorMessage: string))
---@global pcall fun(f: (fun(T...): R...), T...): (boolean, R...)

---@global print fun(...): void
---@global rawequal fun(v1: T, v2: T): boolean

-- TODO:
--@global rawget fun(table: table<K, V>, index: (K: nonnil)): ((V: nonnil) | nil)
---@global rawget fun(table: table<K, V>, index: K): V

-- TODO:
--@global rawset fun(table: table<K, V>, index: (K: nonnil), value: ((V: nonnil) | nil)): void
---@global rawset fun(table: table<K, V>, index: K, value: V): void

-- TODO:
--@_Feature select
--@global select ((fun(index: number, T...): R...) | (fun(index: "#", M...): number))
---@global select fun(index: I, T...): R...

-- TODO:
--@global setfenv fun(f: (fun(T...): R...) | number, table: E): void
---@global setfenv fun(f: F, table: E): void

---@global setmetatable fun(table: T, metatable: M): void

-- TODO:
--@global tonumber fun(e: T [, base: number]): (number | nil)
---@global tonumber fun(e: T, ...number): number

---@global tostring fun(e: T): string

-- TODO:
--@global type fun(v: T): ("nil" | "number" | "string" | "boolean" | "table" | "function" | "thread" | "userdata")
---@global type fun(v: T): string

-- TODO:
--@global unpack fun(list: T[] [, i: number [, j: number]]): ...T
---@global unpack fun(list: T[], TBounds...number): ...T

---@global _VERSION string

---@global xpcall fun(f: (fun(): ...), err: (fun(error: string): ...)): (success: boolean, ...)


-- Coroutine Manipulation ----------------------------

---@class StandardCoroutineNamespace
---@generic TInput..., TOutput...
---@field public create fun(f: fun(TInput...): (TOutput...)): thread<TInput..., TOutput...>
-- TODO:
---@generic TInput..., TOutput...
--@field public resume fun(co: thread<TInput..., TOutput...>, TInput...): ((true, TOutput...) | (false, errorMessage: string))
---@field public resume fun(co: thread<TInput..., TOutput...>, TInput...): (boolean, TOutput...)
-- TODO:
---@generic TInput..., TOutput...
--@field public running fun(): (thread<TInput..., TOutput...> | nil)
---@field public running fun(): thread<TInput..., TOutput...>
-- TODO:
---@generic TInput..., TOutput...
--@field public status fun(co: thread<TInput..., TOutput...>): "running" | "suspended" | "normal" | "dead"
---@field public status fun(co: thread<TInput..., TOutput...>): string
---@generic TInput..., TOutput...
---@field public wrap fun(f: fun(TInput...): (TOutput...)): fun(TInput...): (TOutput...)
-- TODO:
---@generic TInput..., TOutput...
---@field public yield fun(TOutput...): (TInput...)

--@_Feature coroutine
---@global coroutine StandardCoroutineNamespace


-- Modules -------------------------------------------

---@global module fun(name: string, ...): void
---@_Feature require
---@global require fun(modname: string): M

---@class StandardPackageNamespace
---@field public cpath string
-- TODO:
---@generic TModule
---@field public loaded table<string, TModule>
---@generic TArgs..., TResults...
---@field public loadlib fun(libname: string, funcname: string): fun(TArgs...): (TResults...)
---@field public path string
---@generic TModule
---@field public preload table<string, fun(modname: string): TModule>
---@generic T
---@field public seeall fun(module: T): void

---@_Feature package
---@global package StandardPackageNamespace


-- String Manipulation -------------------------------

---@_Feature stringMetaTableIndex
---@class StandardStringNamespace
-- TODO:
--@field byte fun(s: string [, i: number [, j: number]]): number
---@field byte fun(s: string, ...number): number
---@field char fun(...number): string
---@generic TInputs..., TOutputs...
---@field dump fun(function: fun(TInputs...): TOutputs...): string
-- TODO:
--@field find fun(s: string, pattern: string [, init: number [, plain: boolean]]): ((start: number, finish: number, ...string) | nil)
---@generic TOptions...
---@generic TCaptures...string
---@field find fun(s: string, pattern: string, TOptions...): (start: number, finish: number, TCaptures...)
---@field format fun(formatstring: string, ...): string
---@field gmatch fun(s: string, pattern: string): (iterator: fun(): ...string,)
-- TODO:
--@field gsub fun(s: string, pattern: string, repl: string | table<string, (number | string | boolean | nil)> | fun:(capture: string, ...string): (number | string | boolean | nil) [, n: number]): string
---@generic Repl
---@field gsub fun(s: string, pattern: string, repl: Repl, ...number): string
---@field len fun(s: string): number
---@field lower fun(s: string): string
-- TODO:
--@field match fun(s: string, pattern: string [, init: number]): ((string, ...string) | nil)
---@generic TInit...number
---@generic TCaptures...string
---@field match fun(s: string, pattern: string, TInit...): (string, TCaptures...)
---@field rep fun(s: string, n: number): string
---@field reverse fun(s: string): string
-- TODO:
--@field sub fun(s: string, i: number [, j: number]): string
---@field sub fun(s: string, i: number, ...number): string
---@field upper fun(s: string): string

---@global string StandardStringNamespace


-- Table Manipulation --------------------------------

---@class StandardTableNamespace
-- TODO:
--@field concat fun(table: V[] [, sep: string, [, i: number [, j: number]]]): string
---@generic V
---@field concat fun(table: V[], ...): string
-- TODO:
--@field insert fun(table: V[], [pos: number ,] value: V): void
---@generic V
---@field insert fun(table: V[], pos: number, value: V): void
---@generic V
---@field maxn fun(table: V[]): number
-- TODO:
--@field remove fun(table: V[], [, pos: number]): (V | nil)
---@generic V
---@field remove fun(table: V[], ...number): V
---@generic V
-- TODO:
--@field sort fun(table: V[], [, comp: fun(V, V): boolean]): void
---@field sort fun(table: V[], ...(fun(V, V): boolean)): void

---@global table StandardTableNamespace


-- Mathematical Functions ----------------------------

---@class StandardMathNamespace
---@field abs fun(x: number): number
---@field acos fun(x: number): number
---@field asin fun(x: number): number
---@field atan fun(x: number): number
---@field atan2 fun(y: number, x: number): number
---@field ceil fun(x: number): number
---@field cos fun(x: number): number
---@field cosh fun(x: number): number
---@field deg fun(x: number): number
---@field exp fun(x: number): number
---@field floor fun(x: number): number
---@field fmod fun(x: number, y: number): number
---@field frexp fun(x: number): (number, number)
---@field huge number
---@field ldexp fun(m: number, e: number): number
---@field log fun(x: number): number
---@field log10 fun(x: number): number
---@field max fun(x: number, ...number): number
---@field min fun(x: number, ...number): number
---@field modf fun(x: number): (number, number)
---@field pi number
---@field pow fun(x: number, y: number): number
---@field rad fun(x: number): number
-- TODO:
--@field random fun([m: number [, n: number]]): number
---@field random fun(...number): number
---@field randomseed fun(x: number): void
---@field sin fun(x: number): number
---@field sinh fun(x: number): number
---@field sqrt fun(x: number): number
---@field tan fun(x: number): number
---@field tanh fun(x: number): number

---@global math StandardMathNamespace


-- Input and Output Facilities -----------------------

---@class StandardFileHandle
---@field close fun(self): void
---@field flush fun(self): void
---@field lines fun(self): (iterator: fun(): string,)
-- TODO:
---@generic TFormats...
---@generic TResults...
---@field read fun(self, TFormats...): TResults...
-- TODO:
--@field seek fun([whence: "set" | "cur" | "end"] [, offset: number]): number
---@field seek fun(self, whence: string, offset: number): number
-- TODO:
--@field setvbuf fun(self, mode: "no" | "full" | "line" [, size: number]): void
---@field setvbuf fun(self, mode: string, ...number): void
-- TODO:
--@field write fun(self, ...(string | number)): void
---@field write fun(self, ...string): void

---@class StandardIONamespace
-- TODO:
--@field close fun([file: StandardFileHandle]): void
---@generic File
---@field close fun(...StandardFileHandle<File>): void
---@field flush fun(): void
-- TODO:
--@field input ((fun(file: string | StandardFileHandle): void) | (fun(): StandardFileHandle)
---@generic File
---@generic TFileOpt..., TInput...StandardFileHandle<File>
---@field input fun(TFileOpt...): (TInput...)
-- TODO:
--@field lines fun([filename: string]): (iterator: fun(): (string | nil),)
---@field lines fun(...string): (iterator: fun(): string,)
-- TODO:
--@field open fun(filename: string [, mode: string]): (((StandardFileHandle,) | (nil, errorMessage: string))
---@generic File
---@field open fun(filename: string, ...string): StandardFileHandle<File>
--@field output ((fun(file: string | StandardFileHandle): void) | (fun(): StandardFileHandle)
---@generic File
---@generic TFileOpt..., TOutput...StandardFileHandle<File>
---@field output fun(TFileOpt...): (TOutput...)
-- TODO:
--@field popen fun([prog: string [, mode: string]]): ((StandardFileHandle,) | (nil, errorMessage: string))
---@generic File
---@field popen fun(...string): StandardFileHandle<File>
-- TODO:
---@generic TFormats...
---@generic TResults...
---@field read fun(TFormats...): TResults...
---@generic File
---@field tmpfile fun(): StandardFileHandle<File>
-- TODO:
--@field type fun(obj: StandardFileHandle): ("file" | "closed file" | nil)
---@generic File
---@field type fun(obj: StandardFileHandle<File>): string
-- TODO:
--@field write fun(...(string | number)): void
---@field write fun(...string): void

---@global io StandardIONamespace


-- Operating System Facilities -----------------------

---@class StandardDateTimeSpecifier
---@field year number
---@field month number
---@field day number

---@class StandardDateTimeInfo : StandardDateTimeSpecifier
---@field hour number
---@field min number
---@field sec number
---@field wday number
---@field yday number
---@field isdst boolean

---@class StandardOSNamespace
---@field clock fun(): number
-- TODO:
--@field date fun([format: string [, time: number]]): (string | StandardDateTimeInfo)
---@field date fun(format: string): string
---@field difftime fun(t2: number, t1: number): (seconds: number,)
-- TODO:
--@field execute fun([command: string]): (status: number,)
---@field execute fun(...string): (status: number,)
-- TODO:
--@field exit fun([code: number]): ...
---@generic Results...
---@field exit fun(...number): Results...
-- TODO:
--@field getenv fun(varname: string): (string | nil)
---@field getenv fun(varname: string): string
-- TODO:
--@field remove fun(filename: string): (() | (nil, errorMessage: string))
---@field remove fun(filename: string): void
-- TODO:
--@field rename fun(oldname: string, newname: string): (() | (nil, errorMessage: string))
---@field rename fun(oldname: string, newname: string): void
-- TODO:
--@field setlocale fun(locale: string [, category: "all" | "collate" | "ctype" | "monetary" | "numeric" | "time"]): string | nil
---@field setlocale fun(locale: string, ...string): string
-- TODO:
--@field time fun([table: TDate]): number
-- TODO:
--@generic TDate: StandardDateTimeSpecifier
---@generic TDate: { year: number, month: number, day: number }
---@field time fun(table: TDate): number
---@field tmpname fun(): string

---@global os StandardOSNamespace


-- The Debug Library ---------------------------------

---@class StandardDebugNamespace
---@field debug fun(): void
---@generic Object, Environment
---@field getfenv fun(o: Object): Environment
---@field gethook fun(): (hook: (fun(string, ...number): void), mask: string, count: number)
-- TODO:
---@field getinfo fun(function: FunctionOrLevel, ...string): Info
---@generic Value
---@field getlocal fun(level: number, localIndex: number): (name: string, value: Value)
---@generic Object, MetaTable
---@field getmetatable fun(object: Object): MetaTable
---@generic Table
---@field getregistry fun(): Table
---@generic Value, Args..., Results...
---@field getupvalue fun(func: (fun(Args...): Results...), up: number): (string, Value)
---@generic Object, Environment
---@field setfenv fun(object: Object, table: Environment): void
-- TODO:
--@field sethook fun(hook: fun(event: string [, line: number]): void, mask: string [, count: number]): void
---@field sethook fun(hook: fun(event: string, ...number): void, mask: string, ...number): void
-- TODO:
--@field setlocal fun(level: number, localIndex: number, value: Value): string | nil
---@generic Value
---@field setlocal fun(level: number, localIndex: number, value: Value): string
---@generic Object, MetaTable
---@field setmetatable fun(object: Object, table: MetaTable): void
-- TODO:
--@field setupvalue(func: fun(...Args): ...Results, up: number, value: Value): string | nil
---@generic Args..., Results..., Value
---@field setupvalue fun(func: fun(Args...): Results..., up: number, value: Value): string
-- TODO:
--@field traceback fun([message: string]): string
---@field traceback fun(...string): string

---@global debug StandardDebugNamespace
