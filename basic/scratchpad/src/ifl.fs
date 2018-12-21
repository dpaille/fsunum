(*
    Copyright (c) 2018 Daniel Paillé

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*)

namespace fsunum


module ifl =
    open System
    open System.IO
    open uint128
    open df

    type ISingleton =
        abstract member Singleton : ISingleton
    type IFloat< 'F > =
        abstract member IsNaN : 'F -> bool
        abstract member IsInf : 'F -> bool
        abstract member create : float -> 'F
        abstract member Pow : 'F * 'F -> 'F
        abstract member abs : 'F -> 'F
        abstract member acos : 'F -> 'F
        abstract member acoh : 'F -> 'F
        abstract member asin : 'F -> 'F
        abstract member asinh : 'F -> 'F
        abstract member atan : 'F -> 'F
        abstract member Atan2 : 'F * 'F -> 'F
        abstract member atanh : 'F -> 'F
        abstract member ceil : 'F -> 'F
        abstract member cos : 'F -> 'F
        abstract member cosh : 'F -> 'F
        abstract member exp : 'F -> 'F
        abstract member float : 'F -> float
        abstract member floor : 'F -> 'F
        abstract member from : float -> 'F
        abstract member fromul : uint64 -> 'F
        abstract member touint128 : 'F -> uint128
        abstract member id : 'F -> 'F
        abstract member E : 'F
        abstract member Eps : float
        abstract member Log10 : 'F
        abstract member Log2 : 'F
        abstract member NaN : 'F
        abstract member PosInf : 'F
        abstract member NegInf : 'F
        abstract member One : 'F
        abstract member MinusOne : 'F
        abstract member OneHundredEighty : 'F
        abstract member ThreeHundredSixty : 'F
        abstract member Pi : 'F
        abstract member PiOverFour : 'F
        abstract member PiOverTwo : 'F
        abstract member Ten : 'F
        abstract member ThreePiQuarter : 'F
        abstract member TwoPi : 'F
        abstract member Zero : 'F
        abstract member MantissaBitsNb : int
        abstract member log : 'F -> 'F
        abstract member log2 : 'F -> 'F
        abstract member log10 : 'F -> 'F
        abstract member nint : 'F -> 'F
        abstract member Npwr : 'F * int -> 'F
        abstract member Nroot : 'F * int -> 'F
        abstract member plusrfloat : 'F * float -> 'F
        abstract member pluslfloat : float * 'F -> 'F
        abstract member plus : 'F * 'F -> 'F
        abstract member  divides : 'F * 'F -> 'F
        abstract member  dividesrfloat : 'F * float -> 'F
        abstract member  divideslfloat : float * 'F -> 'F 
        abstract member times: 'F * 'F -> 'F
        abstract member  timesrfloat : 'F * float -> 'F
        abstract member  timeslfloat : float * 'F -> 'F 
        abstract member minus: 'F * 'F -> 'F
        abstract member minusrfloat: 'F * float -> 'F
        abstract member minuslfloat: float * 'F -> 'F
        abstract member negate : 'F -> 'F
        abstract member polyeval : 'F list * int * 'F -> 'F
        abstract member polyroot : 'F list * int * 'F * int option * float option -> 'F
        abstract member pow : 'F * 'F -> 'F
        //abstract member print : System.IO.TextWriter -> 'F -> unit
        abstract member rand : unit -> float
        abstract member sin : 'F -> 'F
        abstract member sinh : 'F -> 'F
        abstract member sprint : 'F -> string
        abstract member sqr : 'F -> 'F
        abstract member sqrt : 'F -> 'F
        abstract member tan : 'F -> 'F
        abstract member tanh : 'F -> 'F

    type FloatExpression< 'F >  =
        | Expr of FloatExpression<'F>
        | Val of 'F
        | From of float
        | FromUL of uint64
        | Plus of FloatExpression<'F> * FloatExpression<'F>
        | PlusRF of FloatExpression<'F> * float
        | PlusLF of float * FloatExpression<'F>
        | Minus of FloatExpression<'F> * FloatExpression<'F>
        | MinusRF of FloatExpression<'F> * float
        | MinusLF of float * FloatExpression<'F>
        | Times of FloatExpression<'F> * FloatExpression<'F>
        | TimesRF of FloatExpression<'F> * float
        | TimesLF of float * FloatExpression<'F>
        | Divides of FloatExpression<'F> * FloatExpression<'F>
        | DividesRF of FloatExpression<'F> * float
        | DividesLF of float * FloatExpression<'F>
        | Power of FloatExpression<'F> * FloatExpression<'F>
        | Abs of FloatExpression<'F>
        | Acos of FloatExpression<'F> 
        | Acoh of FloatExpression<'F> 
        | Asin of FloatExpression<'F> 
        | Asinh of FloatExpression<'F>
        | Atan of FloatExpression<'F> 
        | Atan2 of FloatExpression<'F> * FloatExpression<'F>
        | Atanh of FloatExpression<'F>
        | Ceil of FloatExpression<'F> 
        | Cos of FloatExpression<'F> 
        | Cosh of FloatExpression<'F> 
        | Exp of FloatExpression<'F> 
        | Floor of FloatExpression<'F> 
        | Log of FloatExpression<'F> 
        | Log2 of FloatExpression<'F> 
        | Log10 of FloatExpression<'F> 
        | Negate of FloatExpression<'F> 
        | Nint of FloatExpression<'F> 
        | Npwr of FloatExpression<'F> * int
        | Nroot of FloatExpression<'F> * int
        | Sin of FloatExpression<'F> 
        | Sinh of FloatExpression<'F> 
        | Sqr of FloatExpression<'F> 
        | Sqrt of FloatExpression<'F> 
        | Tan of FloatExpression<'F> 
        | Tanh of FloatExpression<'F> 
        member this.Eval (ifl : IFloat<'F>) = 
            let rec evalExp exp =
                match exp with
                    | Expr(x) -> evalExp x
                    | Val(x) -> ifl.id x // -> x
                    | From(x) -> ifl.from x
                    | FromUL(x) -> ifl.fromul x
                    | PlusRF(lhs, rhs) -> let lhsv = evalExp lhs in ifl.plusrfloat (lhsv, rhs)
                    | PlusLF(lhs, rhs) -> let rhsv = evalExp rhs in  ifl.pluslfloat (lhs, rhsv)
                    | Plus(lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.plus (lhsv, rhsv)
                    | MinusRF(lhs, rhs) -> let lhsv = evalExp lhs in ifl.minusrfloat (lhsv, rhs)
                    | MinusLF(lhs, rhs) -> let rhsv = evalExp rhs in ifl.minuslfloat (lhs, rhsv)
                    | Minus(lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.minus (lhsv, rhsv)
                    | TimesRF(lhs, rhs) -> let lhsv = evalExp lhs in ifl.timesrfloat (lhsv, rhs)
                    | TimesLF(lhs, rhs) -> let rhsv = evalExp rhs in ifl.timeslfloat (lhs, rhsv)
                    | Times(lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.times (lhsv, rhsv)
                    | DividesRF(lhs, rhs) -> let lhsv = evalExp lhs in ifl.dividesrfloat (lhsv, rhs)
                    | DividesLF(lhs, rhs) -> let rhsv = evalExp rhs in ifl.divideslfloat (lhs, rhsv)
                    | Divides(lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.divides (lhsv, rhsv)
                    | Abs(x) -> let xv = evalExp x in ifl.abs xv
                    | Acos(x) -> let xv = evalExp x in ifl.acos xv
                    | Acoh(x) -> let xv = evalExp x in ifl.acoh xv 
                    | Asin(x) -> let xv = evalExp x in ifl.asin xv
                    | Asinh(x) -> let xv = evalExp x in ifl.asinh xv
                    | Atan(x) -> let xv = evalExp x in ifl.atan xv
                    | Atan2(y, x) -> let yv, xv = evalExp y, evalExp x in ifl.Atan2 (yv, xv)
                    | Atanh(x) -> let xv = evalExp x in ifl.atanh xv
                    | Ceil(x) -> let xv = evalExp x in ifl.ceil xv
                    | Cos(x) -> let xv = evalExp x in ifl.cos xv
                    | Cosh(x) -> let xv = evalExp x in ifl.cosh xv
                    | Exp(x) -> let xv = evalExp x in ifl.exp xv
                    | Floor(x) -> let xv = evalExp x in ifl.floor xv
                    | Log(x) -> let xv = evalExp x in ifl.log xv
                    | Log2(x) -> let xv = evalExp x in ifl.log2 xv
                    | Log10(x) -> let xv = evalExp x in ifl.log10 xv
                    | Negate(x) -> let xv = evalExp x in ifl.negate xv
                    | Nint(x) -> let xv = evalExp x in ifl.nint xv
                    | Npwr(x, y) -> let xv = evalExp x in ifl.Npwr (xv, y)
                    | Nroot(x, y) -> let xv = evalExp x in ifl.Nroot (xv, y)
                    | Power(x, y) -> let xv, yv = evalExp x, evalExp y in ifl.Pow (xv, yv)
                    | Sin(x) -> let xv = evalExp x in ifl.sin xv
                    | Sinh(x) -> let xv = evalExp x in ifl.sinh xv
                    | Sqr(x) -> let xv = evalExp x in ifl.sqr xv
                    | Sqrt(x) -> let xv = evalExp x in ifl.sqrt xv
                    | Tan(x) -> let xv = evalExp x in ifl.tan xv
                    | Tanh(x) -> let xv = evalExp x in ifl.tanh xv
                    //| _ -> failwith "FloatExpression: unknown operation."
            evalExp this
        static member (~-) (x) = Negate (x)
        static member (+) (lhs, rhs : float) = PlusRF (lhs, rhs)
        static member (+) (lhs : float, rhs) = PlusLF (lhs, rhs)
        static member (+) (lhs, rhs) = Plus (lhs, rhs)
        static member (-) (lhs, rhs : float) = MinusRF (lhs, rhs)
        static member (-) (lhs : float, rhs) = MinusLF (lhs, rhs)
        static member (-) (lhs, rhs) = Minus (lhs, rhs)
        static member (*) (lhs, rhs : float) = TimesRF (lhs, rhs)
        static member (*) (lhs : float, rhs) = TimesLF (lhs, rhs)
        static member (*) (lhs, rhs) = Times (lhs, rhs)
        static member (/) (lhs, rhs : float) = DividesRF (lhs, rhs)
        static member (/) (lhs : float, rhs) = DividesLF (lhs, rhs)
        static member (/) (lhs, rhs) = Divides (lhs, rhs)
        //static member (!**) (lhs, rhs) = Power (lhs, rhs)
        static member Pow (lhs, rhs) = Power (lhs, rhs)
        //static member (!**) (lhs, rhs : int) = if rhs = 2 then Sqr (lhs) else Npwr (lhs, rhs)
        static member Pow (lhs, rhs : int) = Npwr (lhs, rhs)

    type FloatExpressionBool<'F when 'F : comparison> =
        | Not of FloatExpressionBool<'F >
        | And of FloatExpressionBool<'F > * FloatExpressionBool<'F >
        | Or of FloatExpressionBool<'F > * FloatExpressionBool<'F >
        | LessThan of  FloatExpression<'F > * FloatExpression<'F >
        | GreaterThan of  FloatExpression<'F > * FloatExpression<'F >
        | Equal of  FloatExpression<'F > * FloatExpression<'F >

        member this.Test (ifl : IFloat<'F>) : bool =
            let rec testExp exp =
                match exp with
                    | Not x -> not (testExp x)
                    | And (lhs, rhs) -> testExp lhs && testExp rhs
                    | Or (lhs, rhs) -> testExp lhs || testExp rhs
                    | LessThan (lhs, rhs) -> let lhsv, rhsv = lhs.Eval ifl, rhs.Eval ifl in lhsv < rhsv
                    | GreaterThan (lhs, rhs) -> let lhsv, rhsv = lhs.Eval ifl, rhs.Eval ifl in lhsv > rhsv
                    | Equal (lhs, rhs) -> let lhsv, rhsv = lhs.Eval ifl, rhs.Eval ifl in lhsv = rhsv
            testExp this

        static member not (lhs) = Not lhs
        static member op_BooleanAnd (lhs , rhs) = And (lhs, rhs)
        static member op_BooleanOr (lhs , rhs) = And (lhs, rhs)
        static member op_LessThan (lhs , rhs) = LessThan (lhs, rhs)
        static member op_GreaterThan (lhs , rhs) = GreaterThan (lhs, rhs)
        static member op_Equality (lhs , rhs) = Equal (lhs, rhs)

    type SPFloat private () =
        static let random = Random()

        static let E_ = exp 1.
        static let Eps_ = 2. ** -53.
        static let Log10_ = log 10.
        static let Log2_ = log 2.
        static let One_ = 1.
        static let MinusOne_ = -1.
        static let OneHundredEighty_ = 180.
        static let ThreeHundredSixty_ = 360.
        static let Pi_ = Math.PI // 4. * atan 1.
        static let PiOverFour_ =  Math.PI / 4. // atan 1.
        static let PiOverTwo_ = Math.PI / 2. // 2. * atan 1.
        static let Ten_ = 10.
        static let ThreePiQuarter_ = 3. * Math.PI / 4. // 3. * atan 1.
        static let TwoPi_ =  Math.PI * 2. // 8. * atan 1.
        static let Zero_ = 0.

        static member IFloat = SPFloat() :> IFloat<_>

        interface IFloat<float> with
            override this.NaN = Double.NaN
            override this.PosInf = Double.PositiveInfinity
            override this.NegInf = Double.NegativeInfinity
            override this.IsNaN x = Double.IsNaN x
            override this.IsInf x = Double.IsInfinity x
            override this.create x = x
            override this.Pow (x, y) = x ** y
            override this.abs x = abs x
            override this.acos x = acos x
            override this.acoh x =
                let ifloat = this :> IFloat<_>
                if x < 1. then
                    printfn "float.acoh: Argument out of domain."
                    ifloat.NaN
                else  log (x + sqrt(ifloat.sqr x - 1.))

            override this.asin x = asin x
            override this.asinh x =
                let ifloat = this :> IFloat<_>
                log (x + sqrt(ifloat.sqr x + 1.))
            override this.atan x = atan x
            override this.Atan2 (y, x) = atan2 y x
            override this.atanh x =
                if abs x >= 1. then
                    printfn "float.atanh: Argument out of domain."
                    Double.NaN
                else (log ((1. + x) / (1. - x))) * 0.5

            override this.ceil x = ceil x
            override this.cos x = cos x
            override this.cosh x = Math.Cosh x
            override this.exp x = exp x
            override this.id x = x
            override this.float x = x
            override this.floor x = floor x
            override this.from x = x
            override this.fromul x = float x
            // YOU SHOULD NOT USE THIS METHOD 
            // IT ONLY EXISTS BECAUSE OF THE IFLOAT INTERFACE
            // AND IT ONLY MAKES SENSE FOR DFLOAT (106 bits of fraction) AND QFLOAT (212 bits of fraction)  
            override this.touint128 f =
                    let fi = floor f
                    let max = 2. ** 128.
                    if fi > max then
                        failwith "float.touint128: float too big to be converted to uint128."
                    else
                        let maxu = 2. ** 64.
                        let hi = floor (fi / maxu)
                        let lo = fi - maxu * hi
                        // WRONG: unfortunately a float can only represent 52 bits of an integer and not 64.
                        // So the following can lead to a loss of precision
                        if hi > (2. ** 52.) || lo > (2. ** 52.)  then
                            failwith "float.touint128: loosing precision converting a float to an uint64"
                        uint128 (uint64 hi, uint64 lo)

            override this.E = E_
            override this.Eps = Eps_
            override this.Log10 = Log10_
            override this.Log2 = Log2_
            override this.One = One_
            override this.MinusOne = MinusOne_
            override this.OneHundredEighty = OneHundredEighty_ 
            override this.ThreeHundredSixty = ThreeHundredSixty_
            override this.Pi = Pi_
            override this.PiOverFour = PiOverFour_
            override this.PiOverTwo = PiOverTwo_
            override this.Ten = Ten_
            override this.ThreePiQuarter = ThreePiQuarter_
            override this.TwoPi = TwoPi_
            override this.Zero = Zero_
            override this.MantissaBitsNb = 52
            override this.log x = log x
            override this.log2 x = Math.Log(x, 2.)
            override this.log10 x = Math.Log10 x
            override this.nint x = if x = floor x then x else floor (x + 0.5)
            override this.Npwr (x, n) = pown x n
            override this.Nroot (x, n) =
                // Strategy:  Use Newton iteration for the function
                //
                //  f(x) = x^(-n) - a
                //
                //  to find its root a^{-1/n}.  The iteration is thus
                //
                //  x' = x + x * (1 - a * x^n) / n
                //
                //  which converges quadratically.  We can then find 
                //  a^{1/n} by taking the reciprocal.
                //
                let ifloat = this :> IFloat<_>
                match x, n with
                | _,n when n <= 0 ->
                    printfn "nroot: N must be positive."
                    Double.NaN
                | x, n when x < 0. && n%2 = 0 ->
                    printfn "nroot: Negative argument."
                    Double.NaN
                | x, n when n = 1 -> x
                | x, n when n = 2 -> sqrt x
                | x, _ when x < 0. -> 0.
                | x, n ->
                    // Note  a^{-1/n} = exp(-log(a)/n)
                    let r = abs x
                    let x_ = exp( -(log r) / float n )
                    // Perform Newton's iteration.
                    let x1 = x_ + x_ * (1. - r * ifloat.Npwr (x_, n)) / float n
                    let x2 = if x < 0. then -x1 else x1
                    1. / x2

            override this.plusrfloat (x, y : float) = x + y
            override this.pluslfloat (x: float, y ) = x + y
            override this.plus (x, y) = x + y
            override this. divides (x, y) = x / y
            override this. dividesrfloat (x, y:float) = x / y
            override this. divideslfloat (x:float, y) = x / y
            override this.times (x, y) = x * y
            override this.timesrfloat (x, y:float) = x * y
            override this.timeslfloat (x:float, y) = x * y
            override this.minus (x, y) = x - y
            override this.minusrfloat (x, y:float) = x - y
            override this.minuslfloat (x:float, y) = x - y
            override this.negate x = -x
            override this. polyeval ( cl : float list, n, x ) =
                // Just use Horner's method of polynomial evaluation.
                let _,r = fWhile (fun (i,r) -> i >= 0)
                            (fun(i,r) ->
                            let r1 = r * x
                            let r2 = r1 + cl.[i]
                            i - 1, r2
                            ) (n - 1, List.last cl)
                r
            override this. polyroot ((cl:float list), n, x0, ?max_iter_, ?thresh_) =
                let ifloat = this :> IFloat<_>
                let max_iter = defaultArg max_iter_ 64
                let thresh = defaultArg thresh_ 0.
                let thresh0 = if thresh = 0. then ifloat.Eps else thresh
                // Compute the coefficients of the derivatives.
                let dl = [ for i in 0..n-1 do yield cl.[i + 1] * double (i + 1) ]
                let max_c = List.fold (fun acc c -> max acc (abs c)) 0. cl
                let thresh1 = thresh0 * max_c
                // Newton iteration.
                let _,x,conv = fWhile (fun (i,x,conv) -> i < max_iter && not conv)
                                    (fun (i,x,conv)->
                                    let f = ifloat.polyeval (cl, n, x)
                                    if abs f < thresh1 then
                                        i + 1, x, true
                                    else
                                        i + 1, x - (f / ifloat.polyeval (dl, n - 1, x)), false
                                    ) (0, x0, false)
                if not conv then
                    printfn "float.polyroot: Failed to converge."
                    Double.NaN
                else
                    x
            override this. pow (x, y) = x ** y
            //override this. print (tw : TextWriter) x =
            //    let ifloat = this :> IFloat<_>
            //    tw.Write( ifloat.sprint x )
            override this. rand () = random.NextDouble()
            override this. sin x = sin x
            override this. sinh x = Math.Sinh x
            override this. sprint x = sprintf "%.*g" 16 x
            override this. sqr x = x * x
            override this. sqrt x = sqrt x
            override this. tan x = tan x
            override this. tanh x = Math.Tanh x

    type SPDFloat private () =
        static let NaN = dfloat.NaN
        static let random = Random()
        static member IFloat = SPDFloat() :> IFloat<_>
        interface IFloat<dfloat> with
            override this.NaN = NaN
            override this.IsNaN x = Double.IsNaN x.hi
            override this.IsInf x = Double.IsInfinity x.hi
            override this.create x = dfloat x
            override this.Pow (x, y) = x ** y
            override this.abs x = dfloat.abs x
            override this.acos x = dfloat.acos x
            override this.acoh x = dfloat.acoh x
            override this.asin x = dfloat.asin x
            override this.asinh x = dfloat.asinh x
            override this.atan x = dfloat.atan x
            override this.Atan2 (y, x) = dfloat.atan2 y x
            override this.atanh x = dfloat.atanh x
            override this.ceil x = dfloat.ceil x
            override this.cos x = dfloat.cos x
            override this.cosh x = dfloat.cosh x
            override this.exp x = dfloat.exp x
            override this.float x = dfloat.float x
            override this.floor x = dfloat.floor x
            override this.id x = x
            override this.from x = dfloat x
            override this.fromul x = dfloat.fromul x
            override this.touint128 x = dfloat.touint128 x
            override this.E = dfloat.E
            override this.Eps = dfloat.Eps
            override this.Log10 = dfloat.Log10
            override this.Log2 = dfloat.Log2
            override this.One = dfloat.One
            override this.MinusOne = dfloat -1.
            override this.OneHundredEighty = dfloat 180.
            override this.ThreeHundredSixty = dfloat 360.
            override this.Pi = dfloat.Pi
            override this.PiOverFour = dfloat.PiOverFour
            override this.PiOverTwo = dfloat.PiOverTwo
            override this.PosInf = dfloat.PosInf
            override this.NegInf = dfloat.NegInf
            override this.Ten = dfloat.Ten
            override this.ThreePiQuarter = dfloat.ThreePiQuarter
            override this.TwoPi = dfloat.TwoPi
            override this.Zero =  dfloat.Zero
            override this.MantissaBitsNb = 104
            override this.log x = dfloat.log x
            override this.log2 x = dfloat.log x / dfloat.Log2
            override this.log10 x = dfloat.log10 x
            override this.nint x = dfloat.Nint x
            override this.Npwr (x, n) = dfloat.npwr x n
            override this.Nroot (x, n) = dfloat.nroot x n

            override this.plusrfloat (x, y : float) = x + y
            override this.pluslfloat (x : float, y) = x + y
            override this.plus (x, y) = x + y
            override this. divides (x, y) = x / y
            override this. dividesrfloat (x, y:float) = x / y
            override this. divideslfloat (x:float, y) = x / y
            override this.times (x, y) = x * y
            override this.timesrfloat (x, y:float) = x * y
            override this.timeslfloat (x:float, y) = x * y
            override this.minus (x, y) = x - y
            override this.minusrfloat (x, y:float) = x - y
            override this.minuslfloat (x:float, y) = x - y
            override this.negate x = -x
            override this. polyeval ( cl : dfloat list, n, x ) = dfloat.polyeval (cl, n, x)
            override this. polyroot ((cl:dfloat list), n, x0, ?max_iter_, ?thresh_) =
                match max_iter_, thresh_ with
                | Some(max_iter), None -> dfloat.polyroot (cl, n, x0, max_iter)
                | Some(max_iter), Some(thresh) -> dfloat.polyroot (cl, n, x0, max_iter, thresh)
                | _, _ -> dfloat.polyroot (cl, n, x0)
            override this. pow (x, y) = x ** y
            //override this. print (tw : TextWriter) x = dfloat.print tw x
            override this. rand () = dfloat.rand()
            override this. sin x = dfloat.sin x
            override this. sinh x = dfloat.sinh x
            override this. sprint x = dfloat.sprint x
            override this. sqr x = dfloat.sqr x
            override this. sqrt x = dfloat.sqrt x
            override this. tan x = dfloat.tan x
            override this. tanh x = dfloat.tanh x
