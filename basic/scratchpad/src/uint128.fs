(*

Copyright (c) 2018 Daniel Paillé

Copyright (c) 2014 Rick Sladkey

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


// A not-so-complete uint128 implementation using built-in uint64
// Note: mostly a port of uint128.cs from  the Dirichlet.Numerics library

module uint128 =
    open System
    type uint128 (hi : uint64, lo : uint64) =
        static let create u =
            uint128 (0UL, u)

        static let Zero_ = create 0UL
        static let One_ = create 1UL
        static let Two_ = create 2UL
        static let MaxValue_ = ~~~ Zero_

        static let add (u : uint128) (v : uint128) =
            let lo = u.lo + v.lo
            let hi = u.hi + v.hi
            let hi1 =
                if lo < u.lo && lo < v.lo then hi + 1UL
                else hi
            uint128 (hi1, lo)

        static let leftshift64 (c : uint128) d =
            if d = 0 then 0UL, c
            else
            let dneg = 64 - d
            let result = c.hi >>> dneg
            let s1 = (c.hi <<< d) ||| (c.lo >>> dneg)
            let s0 = c.lo <<< d
            result, uint128 (s1, s0)

        static let leftshift (c : uint128) d = 
            let res, c1 = 
                if d < 64 then
                    leftshift64 c d
                else
                    let s1 = c.lo <<< (d - 64)
                    let s0 = 0UL
                    0UL, uint128 (s1, s0)
            c1

        static let rightshift64 (c : uint128) d =
            if d = 0 then c
            else
            uint128( c.hi >>> d, (c.hi <<< (64 - d)) ||| (c.lo >>> d))

        static let rightshift (c : uint128) d =
            if d < 64 then
                rightshift64 c d
            else
            uint128( c.hi >>> (d - 64) )

        // float must be positive
        static let create (a : float) =
            if a <= float UInt64.MaxValue then
                uint128 (0UL, uint64 a)
            else
                let shift = Math.Max( int ( Math.Ceiling( Math.Log(a, 2.) ) ) - 63, 0)
                let r0 = uint128 ( 0UL, uint64 (a / Math.Pow(2., float shift)))
                leftshift r0 shift

        static let add (a : uint128) (b : uint128) =
            let sum = a.lo + b.lo
            let a1 = if sum < a.lo && sum < b.lo then a.hi + 1UL else a.hi
            uint128 (a1 + b.hi, sum)

        static let subtract (a : uint128) (b : uint128) =
            let lo = a.lo - b.lo
            let hi = a.hi - b.hi
            if a.lo < b.lo then
                uint128 (hi - 1UL, lo)
            else uint128 (hi, lo)

        static let multiply64 (u : uint64) (v : uint64) =
            let u0 = uint64 (uint32 u)
            let u1 = u >>> 32
            let v0 = uint64 (uint32 v)
            let v1 = v >>> 32
            let carry = u0 * v0
            let r0 = uint64 (uint32 carry)
            let carry0 = (carry >>> 32) + u0 * v1
            let r2 = carry0 >>> 32
            let carry1 = uint64 (uint32 carry0) + u1 * v0
            let lo = (carry1 <<< 32) ||| r0
            let hi = (carry1 >>> 32) + r2 + u1 * v1
            uint128 (hi, lo)

        static let multiply128 (u : uint128) (v : uint64) =
            let w = multiply64 u.lo v
            uint128 (w.hi + u.hi * v, w.lo)

        static let divide64uint (u : uint64) (v : uint32) = uint128 (u / uint64 v)
        static let divide64ulong (u : uint64) (v : uint64) = uint128 (u / v)

        static let divide96uint (u : uint128) (v : uint32) =
            let r2 = u.r2
            let w2 = r2 / v
            let u0 = uint64 (r2 - w2 * v)
            let u0u1 = (u0 <<< 32) ||| uint64 u.r1
            let w1 = uint32 (u0u1 / uint64 v)
            let u0_ = u0u1 - uint64 w1 * uint64 v
            let u0u1_ = (u0_ <<< 32) ||| uint64 u.r0
            let w0 = uint32 (u0u1_ / uint64 v)
            uint128 (uint64 w2, (uint64 w1 <<< 32) ||| uint64 w0)
            
        static let divide128uint (u : uint128) (v : uint32) =
            let r3 = u.r3
            let w3 = r3 / v
            let u0 = uint64 (r3 - w3 * v)
            let u0u1 = (u0 <<< 32) ||| uint64 u.r2
            let w2 = uint32 (u0u1 / uint64 v)
            let u0_a = u0u1 - uint64 w2 * uint64 v
            let u0u1_a = (u0_a <<< 32) ||| uint64 u.r1
            let w1 = uint32 (u0u1_a / uint64 v)
            let u0_b = u0u1_a - uint64 w1 * uint64 v
            let u0u1_b = (u0_b <<< 32) ||| uint64 u.r0
            let w0 = uint32 (u0u1_b / uint64 v)
            uint128 ((uint64 w3 <<< 32) ||| uint64 w2, (uint64 w1 <<< 32) ||| uint64 w0)

        static let divide (u : uint128) (v : uint32) =
            if u.hi = 0UL then
                divide64uint u.lo v
            elif u.hi <= uint64 UInt32.MaxValue then
                divide96uint u v
            else
                divide128uint u v

        static let bitlength (t : uint32) =
            let rec rightshift u count =
                match u with
                | 0u -> count
                | _ -> rightshift (u >>> 1) (count + 1)
            rightshift t 0

        static let getbitlengthuint (v : uint32) =
            let tt = v >>> 16
            if tt <> 0u then
                let t = tt >>> 8
                if t <> 0u then
                    bitlength t + 24
                else
                    bitlength t + 16
            else
                let t = v >>> 8
                if t <> 0u then
                    bitlength t + 8
                else
                    bitlength t

        static let Q (u0 : uint32) (u1 : uint32) (u2 : uint32) (v1 : uint32) (v2 : uint32) =
            let u0u1 = (uint64 u0 <<< 32) ||| uint64 u1
            let qhat = if u0 = u1 then uint64 UInt32.MaxValue else  u0u1 / uint64 v1
            let r = u0u1 - qhat * uint64 v1
            let qh =
                if r = uint64 (uint32 r) && uint64 v2 * qhat > ( (r <<< 32) ||| uint64 u2 ) then
                    let qh0 = qhat - 1UL
                    let r0 = r + uint64 v1
                    if r0 = uint64 (uint32 r0) && uint64 v2 * qh0 > ( (r0 <<< 32) ||| uint64 u2 ) then
                       qh0 - 1UL
                    else
                       qh0
                else
                    qhat
            qh

        static let divrem5 (u0 : uint32) (u1 : uint32) (u2 : uint32) (v1 : uint32) (v2 : uint32) =
            let qhat  = Q u0 u1 u2 v1 v2
            let carry = qhat * uint64 v2
            let borrow = uint64 u2 - uint64 (uint32 carry)
            let carry0 = carry >>> 32
            let u2a = uint32 borrow
            let borrow0 = borrow >>> 32
            let carry1 = carry0 + qhat * uint64 v1
            let borrow1 = borrow0 + uint64 u1 - uint64 (uint32 carry1)

            let carry2 = carry1 >>> 32
            let u1a = uint32 borrow1

            let borrow2 = borrow1 >>> 32
            let borrow3 = borrow2 + uint64 u0 - uint64 (uint32 carry2)
            if borrow3 <> 0UL then
                let qhat0 = qhat - 1UL
                let carry3 = uint64 u2 + uint64 v2
                let u2b = uint32 carry3
                let carry4 = carry3 >>> 32
                let carry5 = carry4 + uint64 u1a + uint64 v1
                let u1b = uint32 carry5
                uint32 u1b, u2b, qhat0
            else
                uint32 u1a, u2a, qhat

        static let divrem7 (u0 : uint32) (u1 : uint32) (u2 : uint32) (u3 : uint32) (v1 : uint32) (v2 : uint32) (v3 : uint32) =
            let qhat  = Q u0 u1 u2 v1 v2
            let carry = qhat * uint64 v3
            let borrow = uint64 u3 - uint64 (uint32 carry)
            let carry0 = carry >>> 32

            let u3a = uint32 borrow
            let borrow0 = borrow >>> 32
            let carry1 = carry0 + qhat * uint64 v2
            let borrow1 = borrow0 + uint64 u2 - uint64 (uint32 carry1)
            let carry2 = carry1 >>> 32

            let u2a = uint32 borrow1
            let borrow2 = borrow1 >>> 32
            let carry3 = carry2 + qhat * uint64 v1
            let borrow3 = borrow2 + uint64 u1 - uint64 (uint32 carry3)
            let carry4 = carry3 >>> 32

            let u1a = uint32 borrow3
            let borrow4 = borrow3 >>> 32
            let borrow5 = borrow4 + uint64 u0 - uint64 (uint32 carry4)

            if borrow5 <> 0UL then
                let qhat0 = qhat - 1UL
                let carry5 = uint64 u3 + uint64 v3
                let u3b = uint32 carry5
                let carry6 = carry5 >>> 32
                let carry7 = carry6 + uint64 u2a + uint64 v2

                let u2b = uint32 carry7
                let carry8 = carry7 >>> 32
                let carry9 = carry8 + uint64 u1a + uint64 v1
                let u1b = uint32 carry9

                uint32 u1b, u2b, u3b, qhat0
            else
                uint32 u1a, u2a, u3a, qhat

        static let divrem9 (u0 : uint32) (u1 : uint32) (u2 : uint32) (u3 : uint32) (u4 : uint32) (v1 : uint32) (v2 : uint32) (v3 : uint32) (v4 : uint32) =
            let qhat  = Q u0 u1 u2 v1 v2
            let carry = qhat * uint64 v4
            let borrow = uint64 u4 - uint64 (uint32 carry)
            let carry0 = carry >>> 32

            let u4a = uint32 borrow
            let borrow0 = borrow >>> 32
            let carry1 = carry0 + qhat * uint64 v3
            let borrow1 = borrow0 + uint64 u3 - uint64 (uint32 carry1)
            let carry2 = carry1 >>> 32

            let u3a = uint32 borrow1
            let borrow2 = borrow1 >>> 32
            let carry3 = carry2 + qhat * uint64 v2
            let borrow3 = borrow2 + uint64 u2 - uint64 (uint32 carry3)
            let carry4 = carry3 >>> 32

            let u2a = uint32 borrow3
            let borrow4 = borrow2 >>> 32
            let carry4 = carry3 + qhat * uint64 v1
            let borrow5 = borrow4 + uint64 u1 - uint64 (uint32 carry4)
            let carry5 = carry4 >>> 32

            let u1a = uint32 borrow5
            let borrow6 = borrow5 >>> 32
            let borrow7 = borrow6 + uint64 u0 - uint64 (uint32 carry5)

            if borrow7 <> 0UL then
                let qhat0 = qhat - 1UL
                let carry6 = uint64 u4 + uint64 v4
                let u4b = uint32 carry6
                let carry7 = carry6 >>> 32
                let carry8 = carry7 + uint64 u3a + uint64 v3

                let u3b = uint32 carry8
                let carry9 = carry8 >>> 32
                let carry10 = carry9 + uint64 u2a + uint64 v2

                let u2b = uint32 carry10
                let carry11 = carry10 >>> 32
                let carry12 = carry11 + uint64 u1a + uint64 v1

                let u1b = uint32 carry12

                uint32 u1b, u2b, u3b, u4b, qhat0
            else
                uint32 u1a, u2a, u3a, u4a, qhat

        static let divide96ulong (u : uint128) (v : uint64) =
            let dneg = getbitlengthuint (uint32 (v >>> 32))
            let d = 32 - dneg
            let vPrime = v <<< d
            let v1 = uint32 (vPrime >>> 32)
            let v2 = uint32 vPrime
            let r0, r1, r2, r3 =
                if d <> 0 then
                    u.r0 <<< 32, (u.r1 <<< d) ||| (u.r0 >>> dneg), (u.r2 <<< d) ||| (u.r1 >>> dneg), u.r2 >>> dneg
                else
                    u.r0, u.r1, u.r2, 0u
            let r2a, r1a, q1 = divrem5 r3 r2 r1 v1 v2
            let r1b, r0a, q0 = divrem5 r2a r1a r0 v1 v2
            uint128 (0UL, (uint64 q1 <<< 32) ||| q0)

        static let divide128ulong (u : uint128) (v : uint64) =
            let dneg = getbitlengthuint (uint32 (v >>> 32))
            let d = 32 - dneg
            let vPrime = v <<< d
            let v1 = uint32 (vPrime >>> 32)
            let v2 = uint32 vPrime
            let r0, r1, r2, r3, r4 =
                if d <> 0 then
                    u.r0 <<< 32, (u.r1 <<< d) ||| (u.r0 >>> dneg), (u.r2 <<< d) ||| (u.r1 >>> dneg), (u.r3 <<< d) ||| (u.r2 >>> dneg), u.r3 >>> dneg
                else
                    u.r0, u.r1, u.r2, u.r3, 0u

            let r3a, r2a, ws1 = divrem5 r4 r3 r2  v1 v2
            let r2b, r1a, q1 = divrem5 r3a r2a r1  v1 v2
            let r1b, r0a, q0 = divrem5 r2b r1a r0 v1 v2
            uint128 (ws1, (uint64 q1 <<< 32) ||| q0)

        static let divideulong (u : uint128) (v : uint64) =
            if u.hi = 0UL then
                divide64ulong u.lo v
            else
                let v0 = uint32 v
                if v = uint64 v0 then
                    if u.hi <= uint64 UInt32.MaxValue then
                        divide96uint u v0
                    else
                        divide128uint u v0
                else
                    if u.hi <= uint64 UInt32.MaxValue then
                        divide96ulong u v
                    else
                        divide128ulong u v

        static let leftshift64_3 (a : uint128) (d : int) =
            if d = 0 then
                0UL, a
            else
            let dneg = 64 - d
            let c0 = uint128 ((a.hi <<< d) ||| (a.lo >>> dneg), a.lo <<< dneg)
            a.hi >>> dneg, c0

        static let divrem96uint128 (rem : uint128) (a : uint128) (b : uint128) =
            let d = 32 - getbitlengthuint b.r2
            let _, v = leftshift64 b d
            let r4_, rem0 = leftshift64_3 a d
            let r4 = uint32 r4_
            let v1 = v.r2
            let v2 = v.r1
            let v3 = v.r0
            let r3 = rem0.r3
            let r2 = rem0.r2
            let r1 = rem0.r1
            let r0 = rem0.r0
            let r3a, r2a, r1a, q1 = divrem7  r4 r3 r2 r1 v1 v2 v3
            let r2b, r1b, r0a, q0 = divrem7 r3a r2a r1a r0 v1 v2 v3
            let rem1 = uint128 (0ul, r2, r1, r0)
            let div = ((uint64 q1) <<< 32) ||| q0
            let rem2 = rightshift64 rem1 d
            rem2, div

        static let divrem128uint128 (rem : uint128) (a : uint128) (b : uint128) =
            let d = 32 - getbitlengthuint b.r3
            let _, v = leftshift64 b d
            let r4_, rem0 = leftshift64_3 a d
            let r4 = uint32 r4_
            let r3 = rem0.r3
            let r2 = rem0.r2
            let r1 = rem0.r1
            let r0 = rem0.r0
            let r3a, r2a, r1a, r0a, div = divrem9  r4 r3 r2 r1 r0 v.r3 v.r2 v.r1 v.r0
            let rem1 = uint128 (r3, r2, r1, r0)
            let rem2 = rightshift64 rem1 d
            rem2, div

        static let divide128 (a : uint128) (b : uint128) =
            if a < b then
                uint128.Zero
            elif b.hi = 0UL then
                divideulong a b.lo
            // divrem96uint128 DOES NOT WORK
            //elif b.hi <= uint64 UInt32.MaxValue then
            //    let rem, div = divrem96uint128 uint128.Zero a b
            //    uint128 div
            else
                let rem, div = divrem128uint128 uint128.Zero a b
                uint128 div

        static let And (a : uint128) (b : uint128) =
            let lo = a.lo &&& b.lo
            let hi = a.hi &&& b.hi
            uint128 (hi, lo)

        static let Or (a : uint128) (b : uint128) =
            let lo = a.lo ||| b.lo
            let hi = a.hi ||| b.hi
            uint128 (hi, lo)

        static let Xor (a : uint128) (b : uint128) =
            let lo = a.lo ^^^ b.lo
            let hi = a.hi ^^^ b.hi
            uint128 (hi, lo)

        static let Not (a : uint128) =
            let lo = ~~~ a.lo
            let hi = ~~~ a.hi
            uint128 (hi, lo)

        member this.lo = lo
        member this.hi = hi
        member private this.r0 : uint32 = uint32 lo
        member private this.r1 : uint32 = uint32 (lo >>> 32)
        member private this.r2 : uint32 = uint32 hi
        member private this.r3 : uint32 = uint32 (hi >>> 32)

        static member Zero = Zero_
        static member One = One_
        static member Two = Two_
        static member MaxValue = MaxValue_

//        static member op_LessThan (lhs , rhs) = LessThan (lhs, rhs)
//        static member op_GreaterThan (lhs , rhs) = GreaterThan (lhs, rhs)
//        static member op_Equality (lhs , rhs) = Equal (lhs, rhs)

        // uint128 + uint128
        static member (+) (a:uint128, b:uint128) = add a b
        // uint128 + uint128
        static member (-) (a:uint128, b:uint128) = subtract a b
        // uint128 <<< int
        static member (<<<) (a:uint128, b:int) = leftshift a b
        // uint128 >>> int
        static member (>>>) (a:uint128, b:int) = rightshift a b
        // uint128 &&& uint64
        //static member (&&&) (a:uint128, b) = uint128 (a.hi, a.lo &&& b)
        // uint128 &&& uint128
        static member (&&&) (a:uint128, b:uint128) = uint128 (a.hi &&& b.hi, a.lo &&& b.lo)
        // uint128 &&& uint64
        //static member (|||) (a:uint128, b) = uint128 (a.hi, a.lo ||| b)
        // uint128 &&& uint128
        static member (|||) (a:uint128, b:uint128) = uint128 (a.hi ||| b.hi, a.lo ||| b.lo)
        // uint128 ^^^ uint64
        //static member (^^^) (a:uint128, b) = uint128 (a.hi, a.lo ^^^ b)
        // uint128 &&& uint128
        static member (^^^) (a:uint128, b:uint128) = uint128 (a.hi ^^^ b.hi, a.lo ^^^ b.lo)
        // not uint128
        static member (~~~) (a:uint128) = Not a
         // convert to bigint DOESN'T WORK ?!?
        static member op_Explicit (u : uint128) : Numerics.BigInteger = 
            let b1 = ((bigint u.hi) <<< 64)
            let b0 = bigint u.lo
            b0 + b1
        static member tobigint (u : uint128) = // bigint u
            let b1 = ((bigint u.hi) <<< 64)
            let b0 = bigint u.lo
            b0 + b1

        // convert to float
        static member op_Explicit (u : uint128) : float = float u.hi * (float UInt64.MaxValue) + float u.lo

        // uint64 * uint128
        static member (*) (a:uint64, b:uint128) = multiply128 b a
        // uint128 * uint64
        static member (*) (a:uint128, b:uint64) = multiply128 a b
        // uint128 / uint64
        static member (/) (a:uint128, b:uint64) = divideulong a b
        // uint128 / uint128
        static member (/) (a:uint128, b:uint128) = divide128 a b

        new (u64) = uint128 (0UL, u64)
        new (r3,r2,r1,r0) =
            let lo = ((uint64 r1) <<< 32) ||| (uint64 r0)
            let hi = ((uint64 r3) <<< 32) ||| (uint64 r2)
            uint128 (hi, lo)

        interface IComparable with
            member this.CompareTo bobj =
                let b = bobj :?> uint128
                if hi > b.hi then 1
                elif hi < b.hi then -1
                else
                if lo > b.lo then 1
                elif lo < b.lo then -1
                else 0
        override this.Equals bobj =
            let b = bobj :?> uint128
            hi = b.hi && lo = b.lo
        override this.GetHashCode() =
            (23 + hi.GetHashCode()) * 31 + lo.GetHashCode()
        override this.ToString() = (uint128.tobigint this).ToString()

