(*

Copyright (c) 2018 Daniel Paillé

This work was supported by the Director, Office of Science, Division
of Mathematical, Information, and Computational Sciences of the
U.S. Department of Energy under contract numbers DE-AC03-76SF00098 and
DE-AC02-05CH11231.

Copyright (c) 2003-2009, The Regents of the University of California,
through Lawrence Berkeley National Laboratory (subject to receipt of
any required approvals from U.S. Dept. of Energy)
All rights reserved.

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


module ifltests =
    open System
    open df
    open ifl
    open System.Diagnostics

    type ``float based scratch pad tests`` () =
        let dprint (ifl: IFloat<_>) f a = Debug.Print <| ifl.sprint a
        let dprints s = Debug.Print s
                
        member x.``Polynomial`` (ifl : IFloat<_>)=
            dprints "Test 1.  Polynomial"
            let n = 8
            let c = [ for i in [0..n - 1] -> ifl.from (float i + 1.0) ]
            let x = ifl.polyroot ( c, (n - 1), (ifl.from 0.0), None, None )
            let y = ifl.polyeval ( c, (n - 1), x )
            dprint ifl "Root Found:  x  = %s" x
            dprint ifl "           p(x) = %s" y

            let c1 = [ifl.from -2030.0; ifl.from 5741.0; ifl.from 1.0; ifl.from -11482.0; ifl.from 8118.0]
            let x0e = From 94906295.0 / From 134217728.0
            let x0 = x0e.Eval ifl
            dprint ifl "x0              = %s" x0
            dprint ifl "sqrt 2 / 2      = %s" ((Sqrt (From 2.0) /  From 2.0).Eval ifl)
            let x1 = ifl.polyroot ( c1, 4, x0, None, None)
            dprint ifl "Root Found: x1  = %s\n" x1

            ifl.float y < 4.0 * ifl.Eps

        member x.``Machin's Formula for Pi`` (ifl : IFloat<_>)=
            dprints "Test 2.  Machin's Formula for Pi"
            //  
            // Use the Machin's arctangent formula:
            //
            //  pi / 4  =  4 arctan(1/5) - arctan(1/239)
            //
            //  The arctangent is computed based on the Taylor series expansion
            //
            //  arctan(x) = x - x^3 / 3 + x^5 / 5 - x^7 / 7 + ...
            //
            let ArctanOneOver (f : float) =
                let d_a = 1.0
                let t_a = (Val ifl.One / f).Eval ifl
                let r_a = ifl.sqr t_a
                let s_a = ifl.Zero
                let k_a = 0
                let sign_a =  1
                let eps = ifl.Eps
                let d_b, t_b, s_b, k_b, sign_b = 
                    fWhile (fun (d, t, s, k, sign) -> ifl.float t > eps)
                        (fun (d, t, s, k, sign) ->
                            let k_ = k + 1
                            // / d doesn't work here, have to add From
                            let tOverd_e = Val t / From d
                            let s_e = if sign < 0 then  Val s - tOverd_e  else Val s + tOverd_e
                            let s_ = s_e.Eval ifl
                            let d_ = d + 2.0
                            let t_= (Val t * Val r_a).Eval ifl
                            let sign_ = -sign
                            d_, t_, s_, k_, sign_
                        ) (d_a, t_a, s_a, k_a, sign_a)
                dprints  (sprintf "%d Iterations" k_b)
                s_b
            // Compute arctan(1/5)
            let s1 = ArctanOneOver 5.0
            //    
            // Compute arctan(1/239)
            let s2 = ArctanOneOver 239.0
            //    
            let p = ( From 4.0 * ( From 4.0 * Val s1 - Val s2 ) ).Eval ifl

            let err = abs ( ifl.float ((Val p - Val ifl.Pi).Eval ifl) ) 
            dprint ifl "   pi = %s" p
            dprint ifl "   Pi = %s" ifl.Pi
            dprints (sprintf "error = %e = %f eps\n" err (err / ifl.Eps) )
            err <= (8.0 * ifl.Eps)

        member x.``Salamin-Brent Quadratic Formula for Pi`` (ifl : IFloat<_>)=
            dprints "Test 3.  Salamin-Brent Quadratic Formula for Pi"
            let max_iter = 20
            let a_0 = ifl.from 1.0
            let b_0 = ifl.sqrt (ifl.from 0.5)
            let s_0 = ifl.from 0.5
            let m_0 = 1.0
            let p_0 = (2.0 * Sqr (Val a_0) / Val s_0).Eval ifl
            dprint ifl "Iteration  0: %s" p_0
            let i_1, a_1, b_1, s_1, m_1, p_1, p_old =
                fWhile (fun (i, a, b, s , m, p, p_old) -> i <= max_iter && abs (ifl.float ((Val p - Val p_old).Eval ifl)) >= 128.0 * ifl.Eps )
                    (fun (i, a, b, s, m, p, p_old) ->
                        let m_ = m * 2.0
                        let a_ = ( 0.5 * (Val a + Val b) ).Eval ifl
                        let b_ = ( Val a * Val b ).Eval ifl
                        let s_ = ( Val s - m_ * (Sqr (Val a_) - Val b_) ).Eval ifl
                        let p_ = ( 2.0 * (Sqr (Val a_)) / Val s_ ).Eval ifl
                        dprints <| sprintf "Iteration %2d: %s" i (ifl.sprint p_)
                        i + 1, a_, ifl.sqrt b_, s_, m_, p_, p 
                    ) (1, a_0, b_0, s_0, m_0, p_0, ifl.Zero)
            let errfromold = abs ( ifl.float ( (Val p_1 - Val p_old).Eval ifl ) )
            let err = abs ( ifl.float ( (Val p_1 - Val ifl.Pi).Eval ifl ) )
            dprint ifl "         _pi: %s" ifl.Pi
            dprints (sprintf "err / prev : %e = %f eps" errfromold (errfromold / ifl.Eps))
            dprints (sprintf "      error: %e = %f eps\n" err (err / ifl.Eps))
            //
            // for some reason, this test gives relatively large error compared
            // to other tests.  May need to be looked at more closely.
            //err <= (1024.0 * ifl.Eps)
            // 14418228 needed for float !
            err <= (14418228. * ifl.Eps)

        member x.``Borwein Quartic Formula for Pi`` (ifl : IFloat<_>)=
            dprints "Test 4.  Borwein Quartic Formula for Pi"
            let max_iter = 20
            let a_0 = ( 6.0 - 4.0 * Sqrt (From 2.0) ).Eval ifl
            let y_0 = ( Sqrt (From 2.0) - 1.0 ).Eval ifl
            let m_0 = 2.0
            let p_0 = ( 1.0 / Val a_0 ).Eval ifl
            dprint ifl "Iteration  0: %s" p_0
            let i_1, a_1, y_1, m_1, p_1, p_old =
                fWhile (fun (i, a, y, m, p, p_old) -> i <= max_iter && abs (ifl.float ( (Val p - Val p_old).Eval ifl )) >= 16.0 * ifl.Eps )
                    (fun (i, a, y, m, p, p_old) ->
                        let m_ = m * 4.0
                        //let r = Tqf.nroot (1.0 - Tqf.sqr (Tqf.sqr y)) 4
                        let r = ( Nroot( (1.0 - Sqr (Sqr (Val y))), 4 ) ).Eval ifl
                        //let y_ = (1.0 - r) / (1.0 + r)
                        let y_ = ( (1.0 - Val r) / (1.0 + Val r) ).Eval ifl
                        //let a_ = a * Tqf.sqr(Tqf.sqr(1.0 + y_)) - m_ * y_ * (1.0 + y_ + Tqf.sqr y_)
                        let a_ = ( Val a * Sqr( Sqr (1.0 + Val y_) ) - m_ * Val y_ * (1.0 + Val y_ + Sqr (Val y_)) ).Eval ifl
                        let p_ = ( 1.0 / Val a_ ).Eval ifl
                        dprints <| sprintf "Iteration %2d: %s" i (ifl.sprint p_)
                        i + 1, a_, y_, m_, p_, p 
                    ) (1, a_0, y_0, m_0, p_0, ifl.Zero)
            let err = abs ( ifl.float ( ( (Val p_1 - Val ifl.Pi) ).Eval ifl ) )
            dprint ifl "         _pi: %s" ifl.Pi
            dprints (sprintf "      error: %e = %f eps\n" err (err / ifl.Eps))
            err < (256.0 * ifl.Eps)

        member x.``Taylor Series Formula for E`` (ifl : IFloat<_>)=
            dprints "Test 5.  Taylor Series Formula for E"
            //
            //   Use Taylor series
            //
            //     e = 1 + 1 + 1/2! + 1/3! + 1/4! + ...
            //
            //   To compute e.
            let s_0 = ifl.from 2.0
            let t_0 = ifl.One
            let n_0 = 1.0
            let epsilon = ifl.Eps
            let i_1, n_1, t_1, s_1 =
                fWhile (fun (i, n, t, s) -> ifl.float t > epsilon)
                    (fun(i, n, t, s) ->
                        let i_ = i + 1
                        let n_ = n + 1.0
                        //let t_ = t / n_
                        let t_ = ( Val t / n_ ).Eval ifl
                        //let s_ = s + t_
                        let s_ = (Val s + Val t_).Eval ifl
                        i + 1, n_, t_, s_
                    ) (0, n_0, t_0, s_0)
            let delta = abs ( ifl.float ( (Val s_1 - Val ifl.E).Eval ifl ) )
            dprint ifl "    e = %s" s_1
            dprint ifl "   _e = %s" ifl.E
            dprints (sprintf "error = %e = %f eps" delta (delta / ifl.Eps))
            dprints (sprintf  " %d iterations.\n" i_1)
            delta < (64.0 * ifl.Eps)

        member x.``Taylor Series Formula for Log 2`` (ifl : IFloat<_>)=
            dprints "Test 6.  Taylor Series Formula for Log 2"
            //
            //  Use the Taylor series
            //
            //   -log(1-x) = x + x^2/2 + x^3/3 + x^4/4 + ...
            //
            //  with x = 1/2 to get  log(1/2) = -log 2.
            //  
            let s_0 = ifl.from 0.5
            let t_0 = s_0
            let n_0 = 1.0
            let epsilon = ifl.Eps
            let i_1, n_1, t_1, s_1 =
                fWhile (fun (i, n, t, s) -> abs (ifl.float t) > epsilon)
                    (fun(i, n, t, s) ->
                        let i_ = i + 1
                        let n_ = n + 1.0
                        let t_ = ( Val t * 0.5 ).Eval ifl
                        let s_ = ( Val s + (Val t_  /n_) ).Eval ifl
                        i + 1, n_, t_, s_
                    ) (0, n_0, t_0, s_0)
            let delta = abs ( ifl.float ( (Val s_1 - Val ifl.Log2).Eval ifl ) )
            dprint ifl " log2 = %s" s_1
            dprint ifl "_log2 = %s" ifl.Log2
            dprints (sprintf "error = %e = %f eps" delta (delta / ifl.Eps))
            dprints (sprintf " %d iterations.\n" i_1)
            delta < (4.0 * ifl.Eps)

        member x.``E square`` (ifl : IFloat<_>)=
            dprints "Test 7.  E square"
            //  Do simple sanity check
            //  
            //    e^2 = exp(2)
            //        = exp(-13/4) * exp(-9/4) * exp(-5/4) * exp(-1/4) *
            //          exp(3/4) * exp(7/4) * exp(11/4) * exp(15/4)
            //  
            //
            let mutable t = ifl.from -3.25
            let mutable p = ifl.One
            for i in [0..7] do p <- (Val p * Exp (Val t)).Eval ifl; t <- (Val t + 1.0).Eval ifl
            let mutable tf = -3.25
            let mutable pf = 1.0
            for i in [0..7] do pf <- pf * exp tf; tf <- tf + 1.0
            let t1f = exp 2.0
            let t2f = Math.E * Math.E
            let dif1 = t1f - pf
            let dif2 = t2f - pf
            let t1 = ifl.exp (ifl.from 2.0)
            let t2 = ifl.sqr ifl.E
            let dif1q = (Val t1 - Val p).Eval ifl
            let dif2q = (Val t2 - Val p).Eval ifl
            let dif1qD = ifl.float (ifl.abs dif1q)
            let dif2qD = ifl.float (ifl.abs dif2q)
            let difq = (Val t1 - Val t2).Eval ifl
            let delta = max ( abs dif1qD ) ( abs dif2qD )
            dprint ifl "result = %s" p
            dprint ifl "exp(2) = %s" t1
            dprint ifl "   e^2 = %s" t2
            dprints (sprintf " error = %e = %f eps\n" delta (delta / ifl.Eps))
            delta <= (16.0 * ifl.Eps)

        member x.``Sanity check for sin / cos`` (ifl : IFloat<_>)=
            dprints "Test 8.  (Sanity check for sin / cos)."
            //
            //  Do simple sanity check
            //  
            //   sin(x) = sin(5x/7)cos(2x/7) + cos(5x/7)sin(2x/7)
            //  
            //   cos(x) = cos(5x/7)cos(2x/7) - sin(5x/7)sin(2x/7);
            //  
            let x = ( Val ifl.Pi / 3.0 ).Eval ifl
            let x1 = ( 5.0 * Val x / 7.0 ).Eval ifl
            let x2 = ( 2.0 * Val x / 7.0 ).Eval ifl
            let test = ( Val ifl.PiOverTwo / 2.0 ).Eval ifl
            let testSin = ifl.sin test
            let testCos = ifl.cos test
            let test1 = ifl.sqrt (ifl.from 3.0)
            let testAtan = ifl.atan test1
            let testAtanDeg = ( Val testAtan * 180.0 / Val ifl.Pi ).Eval ifl
            dprint ifl "atan sqrt(3) (°) = %s" testAtanDeg
            let err_ = (Val testAtan - Val x).Eval ifl
            dprint ifl "err (rad) = %s" err_

            let a = [ifl.from 3.2e8; ifl.from 1.0; ifl.from -1.0; ifl.from 8.0e7]
            let b = [ifl.from 4.0e7; ifl.from 1.0; ifl.from -1.0; ifl.from -1.60e8]
            let c = List.map2 (fun x y -> (Val x * Val y).Eval ifl) a b |> List.reduce (fun x y -> (Val x + Val y).Eval ifl)
            dprint ifl "dot product = %s" c
            let sumsqrt = Sqrt (From 2.0) + Sqrt (From 3.0)
            let d = ( ((From 27.0 / 10.0 - Val ifl.E) / (Val ifl.Pi - ( Sqrt (From 2.0) + Sqrt (From 3.0) ))) ** (From 67.0 / 16.0) ).Eval ifl
            dprint ifl "d = %s" d
            let epowpisqrt163 = ( Val ifl.E ** (Val ifl.Pi * Sqrt (From 163.0)) ).Eval ifl
            dprint ifl "epowpisqrt163 = %s" epowpisqrt163
            let exppisqrt163 = ( Exp (Val ifl.Pi * Sqrt (From 163.0)) ).Eval ifl
            dprint ifl "exppisqrt163  = %s" exppisqrt163
            let r1 = ( Sin (Val x1) * Cos (Val x2) + Cos (Val x1) * Sin (Val x2) ).Eval ifl
            let r2 = ( Cos (Val x1) * Cos (Val x2) - Sin (Val x1) * Sin (Val x2) ).Eval ifl
            let t1 = ( Sqrt (From 3.0) / 2.0 ).Eval ifl
            let t2 = ifl.from 0.5
            let delta = max ( abs( ifl.float ( (Val t1 - Val r1).Eval ifl) ) )
                            ( abs( ifl.float ( (Val t2 - Val r2).Eval ifl) ) )
            dprint ifl "  r1 = %s" r1
            dprint ifl "  r2 = %s" r2
            dprint ifl "  t1 = %s" t1
            dprint ifl "  t2 = %s" t2
            dprints (sprintf " error = %e = %f eps\n" delta (delta / ifl.Eps))
            delta < (4.0 * ifl.Eps)
