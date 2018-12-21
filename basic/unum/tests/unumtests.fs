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


module unumtests =
    open df
    open ifl
    open unum64
    open uboundenv64
    open System.Diagnostics

    type UbDM_f = UboundDM<IEnvironmentDM<float>,float>
    type UbDM_df = UboundDM<IEnvironmentDM<dfloat>,dfloat>
    type Ub_df = Ubound<dfloat>
    type Ubg_df = Uboundg<dfloat>
    type Ubg_f = Uboundg<float>


    type ``Tests from The End Of Error book`` () =
        let dprint (ifl: IFloat<_>) f a = Debug.Print <| ifl.sprint a
        let dprints s = Debug.Print  s

        member x.``Bailey’s numerical nightmare (p. 184) with float (failing)`` () =
            dprints "Bailey’s numerical nightmare (p. 184) with float (failing)\n"

            let af =  25510582.
            let bf =  52746197.
            let cf =  80143857.
            let df = 165707065.
            let uf = 79981812.
            let vf = 251270273.
            let detf = af * df + cf * -bf
            let dxuf = uf * df + vf * -bf
            let dyuf = af * vf + cf * -uf
            let xf = dxuf * detf  
            let yf = dyuf * detf
            dprints (sprintf "xf= %f\n" xf)
            dprints (sprintf "yf= %f\n" yf)
            // float fails to get the x = -1 sol by lack of precision
            xf = 0.

        member x.``Bailey’s numerical nightmare (p. 184) with uboundDM on dfloat`` () =
            dprints "Bailey’s numerical nightmare (p. 184) with uboundDM on dfloat\n"
            let env45d= setenv 4 5 SPDFloat.IFloat
            let ENV45d = new ENVDM<dfloat> (env45d, Some {ubitsmoved = 0; numbersmoved = 0})
            let from = ENV45d.IFrom.from

            let aa = from  25510582.
            let bb = from  52746197.
            let cc = from  80143857.
            let dd = from 165707065.
            let uu = from 79981812.
            let vv = from 251270273.
            let det = UbDM_df.fdot [aa; cc] [dd; -bb]
            let dxu = UbDM_df.fdot [uu; vv] [dd; -bb]
            let dyu = UbDM_df.fdot [aa; cc] [vv; -uu]
            let xx = dxu / det
            let yy = dyu / det
            dprints (sprintf "xx= %A\n" xx)
            dprints (sprintf "yy= %A\n" yy)
            // moved numbers are here 21. Missing the 6 first assigns + 3 negates (?) for a total of 30 as in the book p. 187
            dprints (sprintf "datamoved numbers= %i\n" ENV45d.IEnvironmentDM.DataMoved.Value.numbersmoved)
            dprints (sprintf "datamoved ubits= %i\n" ENV45d.IEnvironmentDM.DataMoved.Value.ubitsmoved)
            let xsol = from  -1.
            let ysol = from  2.
            // got the correct solution
            (xx .= xsol) && (yy .= ysol)

        member x.``Bailey’s numerical nightmare (p. 184) with ubound on dfloat`` () =
            dprints "Bailey’s numerical nightmare (p. 184) with ubound on dfloat\n"
            let env45d= setenv 4 5 SPDFloat.IFloat
            let ENV45d = new ENV<dfloat> (env45d)
            let from = ENV45d.IFrom.from

            let aa = from  25510582.
            let bb = from  52746197.
            let cc = from  80143857.
            let dd = from 165707065.
            let uu = from 79981812.
            let vv = from 251270273.
            let det = Ub_df.fdot [aa; cc] [dd; -bb]
            let dxu = Ub_df.fdot [uu; vv] [dd; -bb]
            let dyu = Ub_df.fdot [aa; cc] [vv; -uu]
            let xx = dxu / det
            let yy = dyu / det
            dprints (sprintf "xx= %A\n" xx)
            dprints (sprintf "yy= %A\n" yy)
            let xsol = from  -1.
            let ysol = from  2.
            // correct solution
            (xx .= xsol) && (yy .= ysol)

        member x.``Bailey’s numerical nightmare (p. 184) with uboundg on dfloat`` () =
            dprints "Bailey’s numerical nightmare (p. 184) with uboundg on dfloat\n"
            let env45d= setenv 4 5 SPDFloat.IFloat
            let ENV45gd = new ENVg<dfloat> (env45d)
            let from = ENV45gd.IFrom.from

            let aa = from  25510582.
            let bb = from  52746197.
            let cc = from  80143857.
            let dd = from 165707065.
            let uu = from 79981812.
            let vv = from 251270273.
            let det = Ubg_df.fdot [aa; cc] [dd; -bb]
            let dxu = Ubg_df.fdot [uu; vv] [dd; -bb]
            let dyu = Ubg_df.fdot [aa; cc] [vv; -uu]
            let xx = dxu / det
            let yy = dyu / det
            dprints (sprintf "xxg= %A\n" xx)
            dprints (sprintf "yyg= %A\n" yy)
            let xsol = from  -1.
            let ysol = from  2.
            (xx .= xsol) && (yy .= ysol)

        member x.``Jean-Michel Muller H function (p. 176) with ubound on dfloat`` () =
            dprints "Jean-Michel Muller H function (p. 176) with ubound on dfloat\n"
            let env45d= setenv 4 5 SPDFloat.IFloat
            let ENV45d = new ENV<dfloat> (env45d)

            let E z = if z .= ENV45d.Zero then ENV45d.One else (Ub_df.exp z - ENV45d.One) / z
            let Q x = let v = Ub_df.sqrt (Ub_df.square x + ENV45d.One) in Ub_df.abs (x - v) - ENV45d.One / (x + v)
            let H x = E ( Ub_df.square (Q x) )

            let hres = [15.; 16.; 17.; 9999.] |> List.map (fun x -> let xu = ENV45d.IFrom.from x in H xu)
            dprints (sprintf "%A\n" hres)
            not ( hres |> List.exists (fun u -> not (u .= ENV45d.One)) )

        member x.``The wrath of Kahan (p. 173) with uboundg on dfloat`` () =
            dprints "The wrath of Kahan (p. 173) with uboundg on dfloat\n"
            let env36d = setenv 3 6 SPDFloat.IFloat
            let ENV36d = new ENVg<dfloat> (env36d)
            let from = ENV36d.IFrom.from
            let u_111 = from 111.
            let u_3000 = from 3000.
            let u_1130 = from 1130.
            let u_2 = from 2.
            let u_m_4 = from -4.
            let _, _, _, sequ =
                fWhile ( fun (i, u0, u1, acc) -> i < 12 )
                    ( fun (i, u0, u1, acc) ->
                    let u2 = u_111 - ( u_1130 / u1) + u_3000 / (u0 * u1)
                    dprints (sprintf "u q (%d) = %A\n" i u2)
                    i + 1, u1, u2, u2 :: acc
                    ) (0, u_2, u_m_4,[])
            let res = List.head sequ
            dprints (sprintf "last = %s" res.ViewUnum)

            // notes:
            // the result is different from the book because:
            // * the 6 bits for fraction size from the book doesn't translate here into 64 bits because we are constrain to a 64 bits unum total
            //   so the sequence fails at iteration 9 (less than 6 result)
            // * therefore the scratchpad layer was used (ENVg type) in order to keep the maximum fraction bits available (106)
            // eventually the sequence will diverge as we runout of precision (at the 29th iteration with dfloat)
            // unum128 from the advanced library are to be used to get the same result as in the book  
            res .< from 7.

        member x.``The quadratic formula (p. 181) with uboundDM on float`` () =
            dprints "The quadratic formula (p. 181) with uboundDM on float\n"
            let envdm35f= setenv 3 5 SPFloat.IFloat
            let ENVDM35f = new ENVDM<float> (envdm35f, Some {ubitsmoved = 0; numbersmoved = 0})
            let from = ENVDM35f.IFrom.from

            let a = from 3.
            let b = from 100.
            let c = from 2.
            let r1u = (UbDM_f.sqrt (UbDM_f.square b - (from 4. * a * c)) - b) /  (from 2. * a)
            dprints <| sprintf "r1u %A\n" r1u
            dprints <| sprintf "r1u %s\n" r1u.ViewUnum
            // with float
            let af = 3.
            let bf = 100.
            let cf = 2.
            let r1f = ( sqrt( bf * bf - 4. * af * cf ) - bf ) / (2. * af)
            dprints <| sprintf "r1f %g\n" r1f
            let sol1 = ENVDM35f.IFrom.fromub (Bounds(38000812971391UL,18555084660UL))
            dprints (sprintf "datamoved numbers= %i\n" ENVDM35f.IEnvironmentDM.DataMoved.Value.numbersmoved)
            dprints (sprintf "datamoved ubits= %i\n" ENVDM35f.IEnvironmentDM.DataMoved.Value.ubitsmoved)
            r1u .= sol1


        member x.``The smooth surprise with uboundg on float`` () =
            dprints "The smooth surprise with uboundg on float\n"
            let env23f = setenv 2 3 SPFloat.IFloat
            let ENV23f = new ENVg<float> (env23f)
            let ifr = ENV23f.IFrom
            let minpower = -5.

            let evaluateU (expr : uint64 -> UboundExpression) (x:Uboundg<'F>) =
                let u = fstBound x.Ubound.Value
                u, (expr u).EvalUBG ifr

            let evaluate expr (ifr:IFrom<_>) ubg0 ubg1 =
                let _, xl, yl =
                    fWhile (fun (x, xl, yl) -> x .< ubg1)
                        (fun (x, xl, yl) ->
                            let u0, y0 = evaluateU expr x
                            let nu = nborhi env23f u0 minpower
                            ifr.fromu nu,  x :: xl, y0 :: yl
                        )
                        (ubg0, [], [])
                xl, yl
            let xl, yl = evaluate  (fun ub -> From 1. + Square( FromU ub ) + Log( Abs(From 1. + From 3. * (From 1. - FromU ub)) ) / From 80. ) ifr (ifr.from 0.8) (ifr.from 2.)
            let neginf = ifr.fromu env23f.neginfu
            yl |> List.exists (fun ub -> let res = ub .= neginf in res)



