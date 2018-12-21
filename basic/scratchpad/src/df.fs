(*

This work was supported by the Director, Office of Science, Division
of Mathematical, Information, and Computational Sciences of the
U.S. Department of Energy under contract numbers DE-AC03-76SF00098 and
DE-AC02-05CH11231.

Copyright (c) 2003-2009, The Regents of the University of California,
through Lawrence Berkeley National Laboratory (subject to receipt of
any required approvals from U.S. Dept. of Energy)
All rights reserved.

Copyright (c) 2018 Daniel Paillé

By downloading or using this software you are agreeing to the modified
BSD license:

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of "The Regents of the University of California" nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

If you wish to use the software for commercial purposes
please contact the Technology Transfer Department at TTD@lbl.gov or
call 510-286-6457.

*)

namespace fsunum

module df =
    open System
    open System.Text
    open System.IO
    open uint128
    open System.Numerics
    open System.Diagnostics

    // utils
    let rec fWhile p f x = if p x then fWhile p f (f x) else x
    let rec fDoWhile f p x = let fx = f x in if p fx then fDoWhile f p fx else fx

    //*********** Basic Functions ************//

    // Computes fl(a+b) and err(a+b).  Assumes |a| >= |b|.
    let inline quick_two_sum (a:float) (b:float) =
        let s = a + b
        let e = b - (s - a)
        s, e

    // Computes fl(a-b) and err(a-b).  Assumes |a| >= |b| 
    let inline quick_two_diff (a:float) (b:float) =
        let s = a - b
        let e = (a - s) - b 
        s, e

    // Computes fl(a+b) and err(a+b).
    let inline two_sum (a:float) (b:float) =
        let s = a + b
        let bb = s - a
        let e = (a - (s - bb)) + (b - bb)
        s, e

    // Computes fl(a-b) and err(a-b).
    let inline two_diff (a:float) (b:float) =
        let d = a - b
        let bb = d - a
        let e = (a - (d - bb)) - (b + bb)
        d, e

    // Computes high word and lo word of a.
    let QD_SPLITTER = 2. ** 27. + 1.
    let QD_SPLIT_THRESH = 2. ** 996.
    let inline split a =
        if a > QD_SPLIT_THRESH || a < - QD_SPLIT_THRESH then
            let a_1 = a * 3.7252902984619140625e-09  // 2^-28
            let temp = QD_SPLITTER * a_1
            let hi = temp - (temp - a_1)
            let lo = a_1 - hi
            let hi_1 = hi * 268435456. // 2^28
            let lo_1 = lo * 268435456.
            hi_1, lo_1
        else
        let t = QD_SPLITTER * a
        let ahi = t - (t - a)
        let alo = a - ahi
        ahi, alo 

    // Computes fl(a*b) and err(a*b). 
    //let inline two_prod a b =
    //    let p = a * b
    //    let ahi, alo = split a
    //    let bhi, blo = split b
    //    let e = ((ahi * bhi - p) + ahi * blo + alo * bhi) + alo * blo
    //    p, e

    // SIMD version
    let inline two_prod a b =
        let p = a * b
        let ahi, alo = split a
        let bhi, blo = split b
        //let e = ((ahi * bhi - p) + ahi * blo + alo * bhi) + alo * blo
        let vec1 = new Vector<float>( [|ahi; ahi; alo; alo|] )
        let vec2 = new Vector<float>( [|bhi; blo; bhi; blo|] )
        let vec3 = vec1 * vec2
        let e = ((vec3.[0] - p) + vec3.[1] + vec3.[2]) + vec3.[3]
        p, e

    // Computes fl(a*a) and err(a*a).  Faster than the above method.
    //let inline two_sqr a =
    //    let p = a * a
    //    let hi, lo = split a
    //    let e = ((hi * hi - p) + 2. * hi * lo) + lo * lo
    //    p, e

    // SIMD version
    let inline two_sqr a =
        //let p = a * a
        let hi, lo = split a
        //let e = ((hi * hi - p) + 2. * hi * lo) + lo * lo
        let vec1 = new Vector<float>( [|hi; 2. * hi; lo; a|] )
        let vec2 = new Vector<float>( [|hi; lo     ; lo; a|] )
        let vec3 = vec1 * vec2
        let e = ((vec3.[0] - vec3.[3]) + vec3.[1] ) + vec3.[2]
        vec3.[3], e
        //p, e

    // Computes the nearest integer to d.
    let inline nint d =
        if d = floor d then d else floor (d + 0.5)

    // dfloat
    type dfloat (hi : float, lo : float) =
        
        //static let dummy = ( new Vector<float> ([|1.;1.;1.;1.|]) ).ToString()

        // dfloat + dfloat
        // This one satisfies IEEE style error bound, due to K. Briggs and W. Kahan.
        static let ieee_add (a:dfloat) (b:dfloat) =
            let s1, s2 = two_sum a.hi b.hi
            let t1, t2 = two_sum a.lo b.lo
            let s2_1 = s2 + t1
            let s1_1, s2_2 = quick_two_sum s1 s2_1
            let s2_3 = s2_2 + t2
            let s1_2, s2_4 = quick_two_sum s1_1 s2_3
            dfloat (s1_2, s2_4)

        // This is the less accurate version ... obeys Cray-style error bound.
        static let sloppy_add (a:dfloat) (b:dfloat) =
            let s, e = two_sum a.hi b.hi
            let e_1 = e + (a.lo + b.lo)
            let s_1, e_2 = quick_two_sum s e_1
            dfloat (s_1, e_2)

        static let ieee_sub (a:dfloat) (b:dfloat) =
            let s1, s2 = two_diff a.hi b.hi
            let t1, t2 = two_diff a.lo b.lo
            let s2_1 = s2 + t1
            let s1_1, s2_2 = quick_two_sum s1 s2_1
            let s2_3 = s2_2 + t2
            let s1_2, s2_4 = quick_two_sum s1_1 s2_3
            dfloat (s1_2, s2_4)

        static let sloppy_sub (a:dfloat) (b:dfloat) =
            let d, e = two_diff a.hi b.hi
            let e_1 = e + a.lo
            let e_2 = e_1 - b.lo
            let s, e_3 = quick_two_sum d e_2
            dfloat (s, e_3)

        static let sub_by_float (a:dfloat) (b:float) =
            let s1, s2 = two_diff a.hi b
            let s2_a = s2 + a.lo
            let s1_a, s2_b = quick_two_sum s1 s2_a 
            dfloat (s1_a, s2_b)

        static let float_sub_by (a:float) (b:dfloat) =
            let s1, s2 = two_diff a b.hi
            let s2_a = s2 - b.lo
            let s1_a, s2_b = quick_two_sum s1 s2_a
            dfloat (s1_a, s2_b)

        static let accurate_div (a:dfloat) (b:dfloat) =
            let q1 = a.hi / b.hi // approximate quotient
            // using overloaded (*) float, dfloat
            let r : dfloat = a - q1 * b
            let q2 = r.hi / b.hi
            // using overloaded (*) float, dfloat
            let r_1 = r - q2 * b
            let q3 = r_1.hi / b.hi
            let q1_1, q2_1 = quick_two_sum q1 q2
            // using overloaded (+) dfloat, float
            let r_2 = dfloat (q1_1, q2_1) + q3
            r_2

        static let sloppy_div (a : dfloat) (b : dfloat) =
            let q1 = a.hi / b.hi // approximate quotient
            // compute  this - q1 * dd
            let r : dfloat = b * q1
            let s1, s2 = two_diff a.hi r.hi
            let s2_a = s2 - r.lo
            let s2_b = s2_a + a.lo
            // get next approximation
            let q2 = (s1 + s2_b) / b.hi
            // renormalize
            let r_hi, r_lo = quick_two_sum q1 q2
            dfloat (r_hi, r_lo)


        // double-double / double
        static let div_by_float (a : dfloat) (b : float) =
            let q1 = a.hi / b // approximate quotient.
            // Compute  this - q1 * d
            let p1, p2 = two_prod q1 b
            let s, e = two_diff a.hi p1
            let e_1 = e + a.lo
            let e_2 = e_1 - p2
            // get next approximation.
            let q2_a = (s + e_2) / b
            // renormalize
            let r_hi, r_lo = quick_two_sum q1 q2_a
            dfloat (r_hi, r_lo)


        static let is_zero (a:dfloat) = a.hi = 0.
        static let is_one (a:dfloat) = a.hi = 1. && a.lo = 0.
        static let is_positive (a:dfloat) = a.hi > 0.
        static let is_negative (a:dfloat) = a.hi < 0.
        static let (|IsZero|_|) a = if is_zero a then Some(a) else None
        static let (|IsPositive|_|) (a:dfloat) = if is_positive a then Some(a) else None
        static let (|IsNegative|_|) (a:dfloat) = if is_negative a then Some(a) else None
        static let is_infinity (a:dfloat) = Double.IsInfinity a.hi
        static let is_nan (a:dfloat) = Double.IsNaN a.hi

        // dfloat * (2. ^ exp)
        static let Ldexp ((a:float), (exp:int)) = a * 2. ** float exp
        static let ldexp ((a:dfloat), exp) = dfloat ( Ldexp(a.hi, exp),  Ldexp(a.lo, exp) )
        // dfloat * float,  where float is a power of 2.
        static let mul_pwr2 (a:dfloat) b = dfloat (a.hi * b, a.lo * b)

        static let n_inv_fact = 15

        static let inv_fact = [|
          dfloat ( 1.66666666666666657e-01,  9.25185853854297066e-18 )
          dfloat ( 4.16666666666666644e-02,  2.31296463463574266e-18 )
          dfloat ( 8.33333333333333322e-03,  1.15648231731787138e-19 )
          dfloat ( 1.38888888888888894e-03, -5.30054395437357706e-20 )
          dfloat ( 1.98412698412698413e-04,  1.72095582934207053e-22 )
          dfloat ( 2.48015873015873016e-05,  2.15119478667758816e-23 )
          dfloat ( 2.75573192239858925e-06, -1.85839327404647208e-22 )
          dfloat ( 2.75573192239858883e-07,  2.37677146222502973e-23 )
          dfloat ( 2.50521083854417202e-08, -1.44881407093591197e-24 )
          dfloat ( 2.08767569878681002e-09, -1.20734505911325997e-25 )
          dfloat ( 1.60590438368216133e-10,  1.25852945887520981e-26 )
          dfloat ( 1.14707455977297245e-11,  2.06555127528307454e-28 )
          dfloat ( 7.64716373181981641e-13,  7.03872877733453001e-30 )
          dfloat ( 4.77947733238738525e-14,  4.39920548583408126e-31 )
          dfloat ( 2.81145725434552060e-15,  1.65088427308614326e-31 )
        |]

        static let pi16 = dfloat (1.963495408493620697e-01, 7.654042494670957545e-18)
        static let sin_table = [|
          dfloat ( 1.950903220161282758e-01, -7.991079068461731263e-18)
          dfloat ( 3.826834323650897818e-01, -1.005077269646158761e-17)
          dfloat ( 5.555702330196021776e-01,  4.709410940561676821e-17)
          dfloat ( 7.071067811865475727e-01, -4.833646656726456726e-17)
        |]

        static let cos_table = [|
          dfloat ( 9.807852804032304306e-01, 1.854693999782500573e-17)
          dfloat ( 9.238795325112867385e-01, 1.764504708433667706e-17)
          dfloat ( 8.314696123025452357e-01, 1.407385698472802389e-18)
          dfloat ( 7.071067811865475727e-01, -4.833646656726456726e-17)
        |]

        // Computes sin(a) using Taylor series.
        // Assumes |a| <= pi/32.
        static let sin_taylor a =
          let thresh = 0.5 * abs(dfloat.float a) * dfloat.Eps
          if is_zero a then dfloat.Zero
          else
              let x = -dfloat.sqr(a);
              let _,s,_,_ =
                fDoWhile (fun (r,s,t,i) ->
                    let r_ = r * x
                    let t = r_ * inv_fact.[i]
                    let s_ = s + t
                    let i_ = i + 2
                    r_, s_, t, i_)
                    (fun(r,s,t,i) -> i < n_inv_fact && abs(dfloat.float t) > thresh)
                    (a,a,dfloat.Zero,0)
              s

        static let cos_taylor a =
            let thresh = 0.5 * dfloat.Eps
            if is_zero a then dfloat.One
            else
                let x = -dfloat.sqr(a);
                let _,s,_,_ =
                    fDoWhile (fun (r,s,t,i) ->
                        let r_ = r * x
                        let t = r_ * inv_fact.[i]
                        let s_ = s + t
                        let i_ = i + 2
                        r_, s_, t, i_)
                        (fun(r,s,t,i) -> i < n_inv_fact && abs(dfloat.float t) > thresh)
                        (x,dfloat.One + mul_pwr2 x 0.5,dfloat.Zero,1)
                s

        static let sincos_taylor a = // outputs sin_a, cos_a
            if is_zero a then dfloat.Zero, dfloat.One
            else
                let sin_a = sin_taylor a
                sin_a, dfloat.sqrt( dfloat.One - dfloat.sqr sin_a)

        // Round to nearest integer
        static let nint (a:dfloat) =
            let hi = nint a.hi
            if hi = a.hi then
                // High word is an integer already.  Round the low word.
                let lo = nint a.lo
                // Renormalize. This is needed if x[0] = some integer, x[1] = 1/2.
                let rhi, rlo = quick_two_sum hi lo in dfloat(rhi, rlo)
            // High word is not an integer.
            elif abs (hi - a.hi) = 0.5 && a.lo < 0. then
                // There is a tie in the high word, consult the low word to break the tie.
                // NOTE: This does not cause INEXACT.
                dfloat ( hi - 1., 0. )
            else
                dfloat ( hi, 0. )

        static let inv a = dfloat.One / a

        static let random = Random()

        static let nbdigits = 31

        // format providers for string output
        static let to_string precision (df : dfloat) =
            if is_nan df then "NaN"
            elif is_infinity df then
                if is_negative df then "-Inf" else "Inf"
            else
            let (digits:string), exponent = df.to_digits (precision)
            let firstdigit =  digits.[0]
            let remainingDigits = digits.[1..(min precision (digits.Length - 1))]
            let remainingDigitsTrimmed = remainingDigits.TrimEnd([|'0'|])
            let exp = sprintf "E%d" exponent
            // point position in the floating part
            let pointPosition = exponent
            let lenWithoutExponent = 
                if pointPosition > remainingDigitsTrimmed.Length then 3 + pointPosition// 1 + remainingDigitsTrimmed.Length + (pointPosition - remainingDigitsTrimmed.Length) + 2
                elif pointPosition < 0 then 2 + (-pointPosition - 1) + 1 + remainingDigitsTrimmed.Length
                else 1 + 1 + remainingDigitsTrimmed.Length
            let lenWithExponent = if remainingDigitsTrimmed.Length = 0 then 2 + exp.Length
                                  else 2 + remainingDigitsTrimmed.Length + exp.Length
            let mant  = if lenWithoutExponent <= lenWithExponent then
                            if pointPosition >= remainingDigitsTrimmed.Length then
                                // 3 + pointPosition // 1 + remainingDigitsTrimmed.Length + (pointPosition - remainingDigitsTrimmed.Length) + 2
                                sprintf "%c%s%s" firstdigit remainingDigitsTrimmed (String('0', pointPosition - remainingDigitsTrimmed.Length))
                            elif pointPosition < 0 then
                                //2 + (-pointPosition - 1) + 1 + remainingDigitsTrimmed.Length
                                sprintf "0.%s%c%s" (String('0', -pointPosition - 1)) firstdigit remainingDigitsTrimmed
                            else 
                                //1 + 1 + remainingDigitsTrimmed.Length
                                if pointPosition = 0 then
                                    sprintf "%c.%s" firstdigit remainingDigitsTrimmed.[0..]
                                else
                                    sprintf "%c%s.%s" firstdigit remainingDigitsTrimmed.[0..pointPosition - 1] remainingDigitsTrimmed.[pointPosition..]
                        else
                            if remainingDigitsTrimmed.Length = 0 then
                                sprintf "%c%s" firstdigit  exp
                            else
                                sprintf "%c.%s%s" firstdigit remainingDigitsTrimmed exp
            let sign = if is_negative df then "-" else "" in sprintf "%s%s" sign mant

        static let Zero_ = dfloat 0.
        static let One_ = dfloat 1.
        static let Ten_ = dfloat 10.
        static let E_ = dfloat (2.718281828459045091, 1.445646891729250158e-16)
        static let Log2_ = dfloat (6.931471805599452862e-01, 2.319046813846299558e-17)
        static let Log10_ = dfloat (2.302585092994045901, -2.170756223382249351e-16)
        static let Pi_ = dfloat (3.141592653589793116, 1.224646799147353207e-16)
        static let ThreePiQuarter_ = dfloat (2.356194490192344837,9.1848509936051484375e-17)
        static let TwoPi_ = dfloat (6.283185307179586232, 2.449293598294706414e-16)
        static let PiOverTwo_ = dfloat (1.570796326794896558, 6.123233995736766036e-17)
        static let PiOverFour_ = dfloat (7.853981633974482790e-01, 3.061616997868383018e-17)
        static let PiOverSixteen_ = dfloat (1.963495408493620697e-01, 7.654042494670957545e-18)
        static let PosInf_ = dfloat Double.PositiveInfinity
        static let NegInf_ = dfloat Double.NegativeInfinity
        static let NaN_ = dfloat Double.NaN

        new (h) = dfloat ( h, 0. )
        new () = dfloat ( 0., 0. )
        member this.hi = hi
        member this.lo = lo
        // dfloat ? dfloat
        interface IComparable with
            member this.CompareTo bobj =
                let b = bobj :?> dfloat
                if Double.IsNaN this.hi then
                    if Double.IsNaN b.hi then 0 else 1
                elif Double.IsNaN b.hi then 1
                else
                    let diffhi = this.hi - b.hi
                    if diffhi <> 0. then //sign diffhi
                        if diffhi < 0. then -1
                        elif diffhi > 0. then 1
                        else 0
                    else
                    let diff = this - b
                    match diff with | IsZero _ -> 0 | IsPositive _ -> 1 | _ -> -1
        override this.Equals bobj =
            let c = (this :> IComparable).CompareTo bobj
            c = 0
        override this.GetHashCode() =
            (23 + hi.GetHashCode()) * 31 + lo.GetHashCode()

        // from uint64
        static member fromul (u:uint64) =
            let f = float u
            let d = u - uint64 f
            if d = 0UL then
                dfloat f
            else
                (dfloat f) + (dfloat (float d))

        static member touint128 (d:dfloat) =
            let di = dfloat.floor d
            let max = dfloat 2. ** 128
            if di > max then
                failwith "dfloat.touint128: dfloat too big to be converted to uint128."
            else
                let converttouint64 y =
                    let rec toul (x:dfloat) u =
                        if x.hi = 0. then
                            u
                        else
                            let xn = x - dfloat (x.hi)
                            toul xn (u + uint64 xn.hi)
                    let yf = dfloat.floor y
                    toul yf (uint64 yf.hi)
                let hidf = dfloat.floor ( di / (dfloat 2. ** 64) )
                let lodf = di - (dfloat 2. ** 64) * hidf
                let hi = converttouint64 hidf
                let lo = converttouint64 lodf
                uint128 (hi, lo)

        // floor
        static member floor (a:dfloat) =
            let hi = floor a.hi
            if hi = a.hi then
                // High word is integer already.  Round the low word.
                let lo = floor a.lo
                let hi1, lo1 = quick_two_sum hi lo
                dfloat (hi1, lo1)
            else dfloat (hi, 0.)

        // ceil
        static member ceil (a:dfloat) =
            let hi = ceil a.hi
            if hi = a.hi then
                // High word is integer already.  Round the low word.
                let lo = ceil a.lo
                let hi1, lo1 = quick_two_sum hi lo
                dfloat (hi1, lo1)
            else dfloat (hi, 0.)

        // nint
        static member Nint (a:dfloat) = nint a

        // dfloat = float + float
        static member add a b = let s, e = two_sum a b in dfloat (s, e)
        // dfloat + dfloat
        static member (+) (a, b) = ieee_add a b
        //static member (+) (a, b) = sloppy_add a b
        // dfloat + float
        static member (+) (a : dfloat, b : float) =
            let s1, s2 = two_sum a.hi b
            let s2_1 = s2 + a.lo
            let s1_1, s2_2 = quick_two_sum s1 s2_1
            dfloat (s1_1, s2_2)
        // float + dfloat (used in log)
        static member (+) (a : float, b : dfloat) = b + a
        // dfloat = float - float
        static member sub a b  = let d, e = two_diff a b in dfloat (d, e)
        // dfloat - dfloat
        //static member (-) (a, b) = sloppy_sub a b
        static member (-) (a, b) = ieee_sub a b
        // dfloat - float
        static member (-) (a, b : float) = sub_by_float a b
        // float - dfloat
        static member (-) (a : float, b) = float_sub_by a b
        // -dfloat
        static member (~-) (a:dfloat) = dfloat(-a.hi, -a.lo)
        // dfloat * dfloat
        static member (*) ((a:dfloat), (b:dfloat)) =
            let p1, p2 = two_prod a.hi b.hi
            let p2_1 = p2 + (a.hi * b.lo + a.lo * b.hi)
            let p1_1, p2_2 = two_sum p1 p2_1
            dfloat (p1_1, p2_2)
        // dfloat * float
        static member (*) ((a:dfloat), (b:float)) =
            let p1, p2 = two_prod a.hi b
            let p2_1 = p2 + a.lo * b
            let p1_1, p2_2 = quick_two_sum p1 p2_1
            dfloat (p1_1, p2_2)
        // float * dfloat
        static member (*) ((a:float), (b:dfloat)) = b * a
        // dfloat / float
        static member (/) ((a:dfloat), (b:float)) =
            div_by_float a b
        static member (/) ((a:dfloat), (b:dfloat)) =
            //sloppy_div a b
            accurate_div a b
        // float / dfloat
        static member (/) ((a:float), (b:dfloat)) = (dfloat a) / b
        static member sqr (a:dfloat) =
            let p1, p2 = two_sqr a.hi
            let p2_1 = p2 + 2. * a.hi * a.lo
            let p2_2 = p2_1 + a.lo * a.lo
            let s1, s2 = quick_two_sum p1 p2_2
            dfloat (s1, s2)
        // cast to float
        static member float (a:dfloat) = a.hi
        // useful constants
        static member Zero = Zero_
        static member One = One_
        static member Ten = Ten_
        static member E = E_
        static member Log2 = Log2_
        static member Log10 = Log10_
        static member Pi = Pi_
        static member ThreePiQuarter = ThreePiQuarter_
        static member TwoPi = TwoPi_
        static member PiOverTwo = PiOverTwo_
        static member PiOverFour = PiOverFour_
        static member PiOverSixteen = PiOverSixteen_
        static member PosInf = PosInf_
        static member NegInf = NegInf_
        static member NaN = NaN_
        static member Eps = 4.93038065763132e-32 // 2^-104

        // sqrt
        static member sqrt a =
            // Strategy:  Use Karp's trick:  if x is an approximation
            //     to sqrt(a), then
            //
            //        sqrt(a) = a*x + [a - (a*x)^2] * x / 2   (approx)
            //
            //     The approximation is accurate to twice the accuracy of x.
            //     Also, the multiplication (a*x) and [-]*x can be done with
            //     only half the precision.
            match a with
            | IsZero _ -> dfloat.Zero
            | IsNegative _ -> dfloat.NaN
            | a ->
                let x = 1. / sqrt a.hi
                let ax = dfloat ( a.hi * x )
                ax + (a - dfloat.sqr ax).hi * (x * 0.5)

        static member abs (a:dfloat) = dfloat ( abs a.hi, a.lo ) 

        // Computes the n-th power of a double-double number.
        // NOTE:  0^0 causes an error.
        static member npwr (a:dfloat) n =
            if n = 0 then
                if is_zero a then
                    Debug.Print "npwr: Invalid argument.\n"
                    dfloat.NaN
                else dfloat.One
            else
                let N0 = abs n
                let s3 = if N0 > 1 then
                            // Use binary exponentiation
                            let _, _, s2 =
                                fWhile (fun (N, r, s) -> N > 0)
                                    (fun (N, r, s) ->
                                        let s1 = if N % 2 = 1 then s * r else s
                                        let N1 = N / 2
                                        let r1 = if N1 > 0 then dfloat.sqr r else r
                                        N1, r1, s1
                                    ) (N0, a, dfloat.One)
                            s2
                         else a
                // Compute the reciprocal if n is negative.
                if n < 0 then dfloat.One / s3 else s3

        // nth root
        // Computes the n-th root of the double-double number a.
        // NOTE: n must be a positive integer.  
        // NOTE: If n is even, then a must not be negative. 
        static member nroot a n =
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
            match a, n with
            | _,n when n <= 0 ->
              Debug.Print  "nroot: N must be positive.\n"
              dfloat.NaN
            | IsNegative a, n when n%2 = 0 ->
              Debug.Print  "nroot: Negative argument.\n"
              dfloat.NaN
            | a, n when n = 1 ->
              a
            | a, n when n = 2 ->
              dfloat.sqrt a
            | IsZero a, _ -> dfloat.Zero
            | a, n ->
            // Note  a^{-1/n} = exp(-log(a)/n)
            let r = dfloat.abs a
            let x = dfloat <| exp( -log(r.hi) / float n )

            // Perform Newton's iteration.
            let x1 = x + x * (dfloat.One - r * dfloat.npwr x n) / dfloat (float n)
            let x2 = if a.hi < 0. then -x1 else x1
            dfloat.One / x2

        // Exponential.  Computes exp(x) in double-double precision. */
        static member exp (a:dfloat) =
        // Strategy:  We first reduce the size of x by noting that
        // 
        //      exp(kr + m * log(2)) = 2^m * exp(r)^k
        //
        // where m and k are integers.  By choosing m appropriately
        // we can make |kr| <= log(2) / 2 = 0.347.  Then exp(r) is 
        // evaluated using the familiar Taylor series.  Reducing the 
        // argument substantially speeds up the convergence.
              let k = 512.;
              let inv_k = 1. / k;

              if a.hi <= -709. then dfloat.Zero
              elif a.hi >= 709. then dfloat.PosInf
              elif is_zero a then dfloat.One
              elif is_one a then dfloat.E
              else
                  let m = floor(a.hi / dfloat.Log2.hi + 0.5)
                  let r = mul_pwr2 (a - dfloat.Log2 * m) inv_k
                  let thresh = inv_k * dfloat.Eps
    
                  let p1 = dfloat.sqr r
                  let s1 = r + mul_pwr2 p1 0.5
                  let p2 = p1 * r
                  let t1 = p2 * inv_fact.[0]
                  let i1 = 0
                  let s00,t00,_,_ = fDoWhile
                                      (fun (s, t, p, i) ->
                                        let s_ = s + t
                                        let p_ = p * r
                                        let i_ = i + 1
                                        let t_ = p_ * inv_fact.[i_]
                                        s_, t_, p_, i_ )
                                      (fun (s, t, p, i) -> abs (dfloat.float t) > thresh && i < 5)
                                      (s1, t1, p2, i1)
                  let s01 = s00 + t00
                  let s02 = mul_pwr2 s01 2. + dfloat.sqr s01
                  let s03 = mul_pwr2 s02 2. + dfloat.sqr s02
                  let s04 = mul_pwr2 s03 2. + dfloat.sqr s03
                  let s05 = mul_pwr2 s04 2. + dfloat.sqr s04
                  let s06 = mul_pwr2 s05 2. + dfloat.sqr s05
                  let s07 = mul_pwr2 s06 2. + dfloat.sqr s06
                  let s08 = mul_pwr2 s07 2. + dfloat.sqr s07
                  let s09 = mul_pwr2 s08 2. + dfloat.sqr s08
                  let s10 = mul_pwr2 s09 2. + dfloat.sqr s09
                  let s11 = s10 + 1.
                  ldexp (s11, int m)

        // Logarithm.  Computes log(x) in double-double precision.
        //   This is a natural logarithm (i.e., base e).
        static member log a =
            // Strategy.  The Taylor series for log converges much more
            // slowly than that of exp, due to the lack of the factorial
            // term in the denominator.  Hence this routine instead tries
            // to determine the root of the function
            //
            //
            //     f(x) = exp(x) - a
            //
            // using Newton iteration.  The iteration is given by
            //
            //     x' = x - f(x)/f'(x) 
            //     = x - (1 - a * exp(-x))
            //     = x + a * exp(-x) - 1.
            //
            // Only one iteration is needed, since Newton's iteration
            // approximately doubles the number of digits per iteration. */
            if is_one a then dfloat.Zero
            elif a.hi <= 0. then
                Debug.Print "dfloat.log: Non-positive argument.\n"
                dfloat.NaN
            else
                let x =  dfloat (log a.hi) // Initial approximation
                let wtf = x + (a * (dfloat.exp -x))
                //let x1 =  x + (a * (dfloat.exp -x)) - 1.
                let x1 =  wtf - 1.
                // one iteration more ( fitted evaluating (10^22+1)/89 )
                let x2 =  x1 + (a * (dfloat.exp -x1)) - 1.
                x2
                //x1

        static member log10 a = dfloat.log a / dfloat.Log10

        static member Pow (a, n) = dfloat.npwr a n
        static member pow (a, b) = dfloat.exp(b * dfloat.log a)
        static member Pow (a : dfloat, b : dfloat) = dfloat.pow (a, b)

        static member sin (a:dfloat) =
            // Strategy.  To compute sin(x), we choose integers a, b so that
            //
            //   x = s + a * (pi/2) + b * (pi/16)
            //
            //   and |s| <= pi/32.  Using the fact that 
            //
            //   sin(pi/16) = 0.5 * sqrt(2 - sqrt(2 + sqrt(2)))
            //
            //   we can compute sin(x) from sin(s), cos(s).  This greatly 
            //   increases the convergence of the sine Taylor series.
            if is_zero a then dfloat.Zero
            else
                // approximately reduce modulo 2*pi
                let z = nint (a / dfloat.TwoPi)
                let r = a - dfloat.TwoPi * z

                // approximately reduce modulo pi/2 and then modulo pi/16.
                let q = floor(r.hi / dfloat.PiOverTwo.hi + 0.5)
                let t = r - dfloat.PiOverTwo * q
                let j = int q
                let q1 = floor(t.hi / dfloat.PiOverSixteen.hi + 0.5)
                let t1 = t - dfloat.PiOverSixteen * q1
                let k = int q1
                let abs_k = abs k

                if j < -2 || j > 2 then
                    Debug.Print  "dfloat.sin: Cannot reduce modulo pi/2.\n"
                    dfloat.NaN

                elif abs_k > 4 then
                    Debug.Print  "dfloat.sin: Cannot reduce modulo pi/16.\n"
                    dfloat.NaN

                elif (k = 0) then
                    match j with
                    | 0 ->  sin_taylor t1
                    | 1 -> cos_taylor t1
                    | -1 -> -cos_taylor t1
                    | _ -> -sin_taylor t1

                else
                    let u = cos_table.[abs_k - 1]
                    let v = sin_table.[abs_k - 1]
                    let sin_t, cos_t = sincos_taylor t1
                    if j = 0 then
                        if k > 0 then
                            u * sin_t + v * cos_t
                        else
                            u * sin_t - v * cos_t
                    elif j = 1 then
                        if k > 0 then
                            u * cos_t - v * sin_t
                        else
                            u * cos_t + v * sin_t
                    elif j = -1 then
                        if k > 0 then
                            v * sin_t - u * cos_t
                        elif k < 0 then
                            -u * cos_t - v * sin_t
                        else r
                    elif k > 0 then
                        -u * sin_t - v * cos_t
                    else
                        v * cos_t - u * sin_t

        static member cos a =
            if is_zero a then dfloat.Zero
            else
                // approximately reduce modulo 2*pi
                let z = nint (a / dfloat.TwoPi)
                let r = a - dfloat.TwoPi * z

                // approximately reduce modulo pi/2 and then modulo pi/16.
                let q = floor(r.hi / dfloat.PiOverTwo.hi + 0.5)
                let t = r - dfloat.PiOverTwo * q
                let j = int q
                let q1 = floor(t.hi / dfloat.PiOverSixteen.hi + 0.5)
                let t1 = t - dfloat.PiOverSixteen * q1
                let k = int q1
                let abs_k = abs k

                if j < -2 || j > 2 then
                    Debug.Print  "dfloat.cos: Cannot reduce modulo pi/2.\n"
                    dfloat.NaN

                elif abs_k > 4 then
                    Debug.Print  "dfloat.cos: Cannot reduce modulo pi/16.\n"
                    dfloat.NaN

                elif (k = 0) then
                    match j with
                    | 0 ->  cos_taylor t1
                    | 1 -> -sin_taylor t1
                    | -1 -> sin_taylor t1
                    | _ -> -cos_taylor t1

                else
                    let u = cos_table.[abs_k - 1]
                    let v = sin_table.[abs_k - 1]
                    let sin_t, cos_t = sincos_taylor t1
                    if j = 0 then
                        if k > 0 then
                            u * cos_t - v * sin_t
                        else
                            u * cos_t + v * sin_t
                    elif j = 1 then
                        if k > 0 then
                            -u * sin_t - v * cos_t
                        else
                            v * cos_t - u * sin_t
                    elif j = -1 then
                        if k > 0 then
                            u * sin_t + v * cos_t
                        else
                            u * sin_t - v * cos_t
                    else
                        if k > 0 then
                            v * sin_t - u * cos_t
                        else
                            -u * cos_t - v * sin_t

        static member sincos a =
            if is_zero a then
                dfloat.Zero, dfloat.One
            else
                // approximately reduce modulo 2*pi
                let z = nint (a / dfloat.TwoPi)
                let r = a - dfloat.TwoPi * z

                // approximately reduce modulo pi/2 and then modulo pi/16.
                let q = floor(r.hi / dfloat.PiOverTwo.hi + 0.5)
                let t = r - dfloat.PiOverTwo * q
                let j = int q
                let abs_j = abs j
                let q1 = floor(t.hi / dfloat.PiOverSixteen.hi + 0.5)
                let t1 = t - dfloat.PiOverSixteen * q1
                let k = int q1
                let abs_k = abs k

                if j < -2 || j > 2 then
                    Debug.Print  "dfloat.sincos: Cannot reduce modulo pi/2.\n"
                    dfloat.NaN, dfloat.NaN

                elif abs_k > 4 then
                    Debug.Print  "dfloat.sincos: Cannot reduce modulo pi/16.\n"
                    dfloat.NaN, dfloat.NaN
                
                else
                    let sin_t, cos_t = sincos_taylor t1
                    let s, c =
                        if abs_k = 0 then
                            sin_t, cos_t
                        else
                            let u = cos_table.[abs_k - 1]
                            let v = sin_table.[abs_k - 1]
                            if k > 0 then
                                u * sin_t + v * cos_t, u * cos_t - v * sin_t
                            else
                                u * sin_t - v * cos_t, u * cos_t + v * sin_t
                    if abs_j = 0 then s, c
                    elif j = 1 then c, -s
                    elif j = -1 then -c, s
                    else -s, -c

        static member atan2 y x =
            // Strategy: Instead of using Taylor series to compute 
            //     arctan, we instead use Newton's iteration to solve
            //     the equation
            //
            //        sin(z) = y/r    or    cos(z) = x/r
            //
            //     where r = sqrt(x^2 + y^2).
            //     The iteration is given by
            //
            //        z' = z + (y - sin(z)) / cos(z)          (for equation 1)
            //        z' = z - (x - cos(z)) / sin(z)          (for equation 2)
            //
            //     Here, x and y are normalized so that x^2 + y^2 = 1.
            //     If |x| > |y|, then first iteration is used since the 
            //     denominator is larger.  Otherwise, the second is used.
            if is_zero x then
                if is_zero y then
                    // Both x and y is zero.
                    Debug.Print  "dfloat.atan2: Both arguments zero.\n"
                    dfloat.NaN
                elif is_positive y then dfloat.PiOverTwo else -dfloat.PiOverTwo
            elif is_zero y then
                if is_positive x then dfloat.Zero else dfloat.Pi
            elif x = y then
                if is_positive y then dfloat.PiOverFour else -dfloat.ThreePiQuarter
            elif x = -y then
                if is_positive y then dfloat.ThreePiQuarter else -dfloat.PiOverFour
            else
                let r = dfloat.sqrt( dfloat.sqr x + dfloat.sqr y )
                let xx = x / r
                let yy = y / r
                // Compute double precision approximation to atan.
                let z = dfloat <| atan2 (dfloat.float y) (dfloat.float x)
                if abs xx.hi > abs yy.hi then
                    // Use Newton iteration 1.  z' = z + (y - sin(z)) / cos(z)
                    let sin_z, cos_z = dfloat.sincos z in z + (yy - sin_z) / cos_z
                else
                    // Use Newton iteration 2.  z' = z - (x - cos(z)) / sin(z)
                    let sin_z, cos_z = dfloat.sincos z in z - (xx - cos_z) / sin_z
  
        static member atan a = dfloat.atan2 a dfloat.One

        static member tan a = let s, c = dfloat.sincos a in s / c

        static member asin a =
            let abs_a = dfloat.abs a
            if abs_a > dfloat.One then
                Debug.Print  "dfloat.asin: Argument out of domain.\n"
                dfloat.NaN
            elif is_one abs_a then
                if is_positive a then dfloat.PiOverTwo else -dfloat.PiOverTwo
            else dfloat.atan2 a (dfloat.sqrt (dfloat.One - dfloat.sqr a))

        static member acos a =
            let abs_a = dfloat.abs a
            if abs_a > dfloat.One then
                Debug.Print  "dfloat.acos: Argument out of domain.\n"
                dfloat.NaN
            elif is_one abs_a then
                if is_positive a then dfloat.Zero else dfloat.Pi
            else dfloat.atan2 (dfloat.sqrt (dfloat.One - dfloat.sqr a)) a

        static member sinh (a:dfloat) =
            if is_zero a then dfloat.Zero
            elif abs ( dfloat.float a ) > 0.05 then
                let ea = dfloat.exp a in mul_pwr2 (ea - inv ea) 0.5
            else
                // since a is small, using the above formula gives
                // a lot of cancellation.  So use Taylor series.
                let r = dfloat.sqr a
                let thresh = dfloat.abs(a) * dfloat.Eps
                let _,s,_ =
                    fDoWhile (fun (m,s,t) ->
                            let m1 = m + 2.
                            let t1 = t * r
                            let t2 = t1 / dfloat ( (m1 - 1.) * m1 )
                            let s1 = s + t2
                            m1, s1, t2
                        )
                        (fun (m,s,t) -> dfloat.abs t > thresh)
                        (1., a, a)
                s

        static member cosh a =
            if is_zero a then dfloat.One
            else let ea = dfloat.exp a in mul_pwr2 (ea + inv ea) 0.5

        static member tanh a =
            if is_zero a then dfloat.Zero
            elif abs ( dfloat.float a ) > 0.05 then
                let ea = dfloat.exp a
                let inv_ea = inv ea
                (ea - inv_ea) / (ea + inv_ea)
            else
                let s = dfloat.sinh a
                let c = dfloat.sqrt (dfloat.One - dfloat.sqr s)
                s / c

        static member sincosh a =
            if abs ( dfloat.float a ) <= 0.05 then
                let s = dfloat.sinh a
                s, dfloat.sqrt (dfloat.One + dfloat.sqr s)
            else
                let ea = dfloat.exp a
                let inv_ea = inv ea
                mul_pwr2 (ea - inv_ea) 0.5, mul_pwr2 (ea + inv_ea) 0.5

        static member asinh a = dfloat.log (a + dfloat.sqrt(dfloat.sqr a + dfloat.One))

        static member acoh a =
            if a < dfloat.One then
                Debug.Print  "dfloat.acoh: Argument out of domain.\n"
                dfloat.NaN
            else dfloat.log (a + dfloat.sqrt(dfloat.sqr a - dfloat.One))

        static member atanh a = 
            if dfloat.abs a >= dfloat.One then
                Debug.Print  "dfloat.atanh: Argument out of domain.\n"
                dfloat.NaN
            else mul_pwr2 (dfloat.log ((dfloat.One + a) / (dfloat.One - a))) 0.5

        static member rand () =
            let m_const = 4.6566128730773926e-10 // = 2^{-31}
            // Strategy:  Generate 31 bits at a time, using lrand48 
            // random number generator.  Shift the bits, and repeat
            // 4 times.
            let _,_,r = fWhile (fun (i,m,r) -> i < 4)
                            (fun(i,m,r) ->
                            let d = random.NextDouble() * m
                            i + 1, m * m_const, r + d
                            ) 
                            (0, m_const, 0.)
            r

        // polyeval(cl, n, x)
        // Evaluates the given n-th degree polynomial at x.
        // The polynomial is given by the array of (n+1) coefficients. */
        static member polyeval ( cl : dfloat list, n, x ) =
            // Just use Horner's method of polynomial evaluation.
            let _,r = fWhile (fun (i,r) -> i >= 0)
                        (fun(i,r) ->
                        let r1 = r * x
                        let r2 = r1 + cl.[i]
                        i - 1, r2
                        ) (n - 1, List.last cl)
            r

        // polyroot(c, n, x0)
        // Given an n-th degree polynomial, finds a root close to 
        // the given guess x0.  Note that this uses simple Newton
        // iteration scheme, and does not work for multiple roots.
        static member polyroot ((cl:dfloat list), n, x0, ?max_iter_, ?thresh_) =
            let max_iter = defaultArg max_iter_ 64
            let thresh = defaultArg thresh_ 0.
            let thresh0 = if thresh = 0. then dfloat.Eps else thresh
            // Compute the coefficients of the derivatives.
            let dl = [ for i in 0..n-1 do yield cl.[i + 1] * double (i + 1) ]
            let max_c = List.fold (fun acc c -> max acc (abs (dfloat.float c))) 0. cl
            let thresh1 = thresh0 * max_c
            // Newton iteration.
            let _,x,conv = fWhile (fun (i,x,conv) -> i < max_iter && not conv)
                                (fun (i,x,conv)->
                                let f = dfloat.polyeval (cl, n, x)
                                if abs (dfloat.float f) < thresh1 then
                                    i + 1, x, true
                                else
                                    i + 1, x - (f / dfloat.polyeval (dl, n - 1, x)), false
                                ) (0, x0, false)
            if not conv then
                Debug.Print  "dfloat.polyroot: Failed to converge.\n"
                dfloat.NaN
            else
                x

        member this.to_digits ?precisionArg =

            let precision = defaultArg precisionArg nbdigits
            let nb_of_digits = if precision > nbdigits || precision < 1 then nbdigits else precision
                               + 1

            let s = StringBuilder()

            let r0 = dfloat.abs this

            if is_zero this then "0", 0
            else

                // First determine the (approximate) exponent. 
                let e = int ( floor (log10 (abs this.hi)))

                let  r =
                    if (e < -300) then
                        let r1 = r0 * (dfloat.Ten ** 300)
                        let r2 = r1 / (dfloat.Ten ** (e + 300))
                        r2
                    elif e > 300 then
                        let r1 = ldexp (r0, -53)
                        let r2 = r1 / (dfloat.Ten ** e)
                        let r3 = ldexp (r0, 53)
                        r3
                    else
                        let r1 = r0 / (dfloat.Ten ** e)
                        r1

                // Fix exponent if we are off by one
                let r_1, e_1 =
                    if r >= dfloat.Ten then r / dfloat.Ten, e + 1
                    elif r < dfloat.One then r * dfloat.Ten, e - 1
                    else r, e

                if r_1 >= dfloat.Ten || r_1 < dfloat.One then
                    Debug.Print  "dfloat.to_digits : can't compute exponent.\n"
                    "ERROR", e_1
                else
                //
                // Extract the digits
                let _, _, l =
                    fWhile (fun (r, i, acc) -> not (is_zero r) && i < nb_of_digits)
                        (fun(r, i, acc) ->
                            let d = int r.hi
                            let r1 = r - (float d)
                            let r2 = r1 * dfloat.Ten
                            r2, i + 1, d :: acc
                        ) (r_1, 0, [])

                let l_1 = List.rev l
                          //|> List.truncate nb_of_digits
                //
                // Fix out of range digits.
                let fixOutOfRangeDigits l = 
                    fWhile (fun nl -> List.exists (fun d -> d > 9 || d < 0) (List.tail nl))
                           (fun nl ->
                            let tailNextList = List.tail nl
                            let differenceListTail = List.map (fun d -> if d > 9 then 1 elif d < 0 then -1 else 0) tailNextList
                            //let decreaseList = List.map (~-)  ( 0 :: differenceListTail )
                            let decreaseList = List.map (fun i -> -10 * i)  ( 0 :: differenceListTail )
                            let leftIncreaseList_ = List.append differenceListTail [0]
                            // allow only increment
                            let leftIncreaseList = List.map (fun d -> if d = -1 then 0 else d) leftIncreaseList_
                            List.map3 (fun a b c -> a + b + c) nl decreaseList leftIncreaseList )
                           l
                let lfixed = fixOutOfRangeDigits l_1
                if List.head lfixed <= 0 then 
                    Debug.Print  "dfloat.to_digits : non-positive leading digit.\n"
                    "ERROR", e_1
                //
                // Round, handle carry.
                elif List.last lfixed >= 5 then
                    let lr_1 = List.mapi
                                   (fun i d -> if i = nb_of_digits - 2 then d + 1
                                               elif i = nb_of_digits - 1 then  0
                                               else d
                                   ) lfixed
                    let lrounded = fixOutOfRangeDigits lr_1
                    let lshifted, e_2 = if List.head lrounded < 10 then lrounded, e_1
                                        else let ls = 1 :: 0 :: List.tail lrounded
                                             ls , e_1 + 1
                    List.iter ( fun (d) -> s.Append(char (d + int '0')) |> ignore ) lshifted
                    s.ToString(), e_2
                else
                    let lshifted, e_2 = if List.head lfixed < 10 then lfixed, e_1
                                        else let ls = 1 :: 0 :: List.tail lfixed
                                             ls , e_1 + 1
                    List.iter ( fun (d) -> s.Append(char (d + int '0')) |> ignore ) lshifted
                    s.ToString(), e_2
                        
          static member sprint (df : dfloat) = to_string nbdigits df
          //static member print (tw : TextWriter) (df : dfloat) = tw.Write( to_string nbdigits df )
          override this.ToString () = dfloat.sprint this
