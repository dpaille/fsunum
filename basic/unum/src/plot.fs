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


module plot =
    open System
    open ifl
    open unum64
    open uboundenv64
    open FSharp.Plotly

    let opacity = 0.4
    let colS = "#00d300"
    let colT = "#d3d300"
    let colF = "#d30000"
    let colSInf = "#00d380"
    let colTInf = "#d3d380"
    let colFInf = "#d30080"
    type ValueType =
        | Solution
        | Trial
        | Failure
    let colForValtype = function | Solution -> colS | Trial -> colT | Failure -> colF
    let maxColForValtype = function | Solution -> colSInf | Trial -> colTInf | Failure -> colFInf
    let maxCol vt x0 x1 y0 y1 = if Double.IsInfinity x0 || Double.IsInfinity x1 || Double.IsInfinity y0 || Double.IsInfinity y1 then
                                   maxColForValtype vt
                                else colForValtype vt

    let plotg env gx gy valtype xs ys inxs inys xlines ylines xrects yrects =
        let ifl = env.ifl
        let ((Lxg,Rxg),(LxB,RxB)) = gx
        let Lx, Rx = ifl.float Lxg, ifl.float Rxg
        let ((Lyg,Ryg),(LyB,RyB)) = gy
        let Ly, Ry = ifl.float Lyg, ifl.float Ryg
        if Double.IsNaN Lx || Double.IsNaN Rx || Double.IsNaN Ly || Double.IsNaN Ry then
            xs, ys, inxs, inys, xlines, ylines, xrects, yrects
        else
            let col = colForValtype valtype
            // exact x
            if Lx = Rx then
                if Ly = Ry then
                    // one possibly exact point
                    if not LyB && not RyB then
                        let xs1, ys1 = Lx :: xs, Ly :: ys
                        xs1, ys1, inxs, inys, xlines, ylines, xrects, yrects
                    else // not exact
                        let inxs1, inys1 = Lx :: Lx :: inxs, Ly :: Ry :: inys
                        xs, ys, inxs1, inys1, xlines, ylines, xrects, yrects
                else
                    // exact point on y ?
                    let xs1, ys1 = if not LyB then Lx :: xs, Ly :: ys
                                   elif not RyB then Lx :: xs, Ry :: ys
                                   else xs, ys
                    // vertical line
                    // 1) inexact points
                    let inxs1, inys1 = Lx :: Lx :: inxs, Ly :: Ry :: inys
                    // 2) line
                    xs1, ys1, inxs1, inys1, Lx :: Lx :: xlines, Ly :: Ry :: ylines, xrects, yrects
            // inexact x, exact y
            elif Ly = Ry then
                // exact point on x ?
                let xs1, ys1 = if not LxB then Lx :: xs, Ly :: ys
                               elif not RxB then Rx :: xs, Ly :: ys
                               else xs, ys
                // horizontal line
                // 1) inexact points
                let inxs1, inys1 = Lx :: Rx :: inxs, Ly :: Ly :: inys
                // 2) line
                xs1, ys1, inxs1, inys1, Lx :: Rx :: xlines, Ly :: Ly :: ylines, xrects, yrects
            // inexact x an y
            else
                // 4 possible exact points
                let xs1, ys1 = if not LxB && not LyB then Lx :: xs, Ly :: ys
                               elif not LxB && not RyB then Lx :: xs, Ry :: ys
                               elif not RxB && not LyB then Rx :: xs, Ly :: ys
                               elif not RxB && not RyB then Rx :: xs, Ry :: ys
                               else xs, ys
                // box
                // 1) inexact points
                let inxs1, inys1 = Lx :: Rx :: inxs, Ly :: Ry :: inys
                // 2) rectangle
                xs1, ys1, inxs1, inys1, xlines, ylines, Lx :: Rx :: xrects, Ly :: Ry :: yrects

    let plotu env (ubx : ubound)(uby : ubound) xs ys shapes =
        let gx, gy = ubound2g env ubx, ubound2g env uby in plotg env gx gy xs ys shapes

    let correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 (title : string option) =
        let minx1 = List.reduce (fun acc x -> if not (Double.IsInfinity x) then min acc x else acc) inxs1
        let minx2 = List.fold (fun acc x -> if not (Double.IsInfinity x) then min acc x else acc) minx1  xs1
        let minx3 = List.fold (fun acc x -> if not (Double.IsInfinity x) then min acc x else acc) minx2 xlines1 
        let minx = List.fold (fun acc x -> if not (Double.IsInfinity x) then min acc x else acc) minx3 xrects1 
        let maxx1 = List.reduce (fun acc x -> if not (Double.IsInfinity x) then max acc x else acc) inxs1
        let maxx2 = List.fold (fun acc x -> if not (Double.IsInfinity x) then max acc x else acc) maxx1 xs1
        let maxx3 = List.fold (fun acc x -> if not (Double.IsInfinity x) then max acc x else acc) maxx2 xlines1 
        let maxx = List.fold (fun acc x -> if not (Double.IsInfinity x) then max acc x else acc) maxx3 xrects1

        let miny1 = List.reduce (fun acc y -> if not (Double.IsInfinity y) then min acc y else acc) inys1
        let miny2 = List.fold (fun acc y -> if not (Double.IsInfinity y) then min acc y else acc) miny1 ys1
        let miny3 = List.fold (fun acc y -> if not (Double.IsInfinity y) then min acc y else acc) miny2 ylines1 
        let miny = List.fold (fun acc y -> if not (Double.IsInfinity y) then min acc y else acc) miny3 yrects1 
        let maxy1 = List.reduce (fun acc y -> if not (Double.IsInfinity y) then max acc y else acc) inys1
        let maxy2 = List.fold (fun acc y -> if not (Double.IsInfinity y) then max acc y else acc) maxy1 ys1
        let maxy3 = List.fold (fun acc y -> if not (Double.IsInfinity y) then max acc y else acc) maxy2 ylines1 
        let maxy = List.fold (fun acc y -> if not (Double.IsInfinity y) then max acc y else acc) maxy3 yrects1

        let correctInf l lo hi =
            List.map (fun x -> if x = Double.PositiveInfinity then hi + (hi - lo) * 0.05
                               elif x = Double.NegativeInfinity then lo - (hi - lo) * 0.05
                               else x ) l

        let xs2 = correctInf xs1 minx maxx
        let ys2 = correctInf ys1 miny maxy
        let inxs2 = correctInf inxs1 minx maxx
        let inys2 = correctInf inys1 miny maxy
        let xlines2 = correctInf xlines1 minx maxx
        let ylines2 = correctInf ylines1 miny maxy
        let xrects2 = correctInf xrects1 minx maxx
        let yrects2 = correctInf yrects1 miny maxy

        let rec makeLines xl yl xol yol shapes =
            let getTwoAndTail l =
                match l with
                | f :: s :: t -> f, s, t
                | _ -> 0., 0., []
            if List.isEmpty xl then shapes
            else
            let hx0, hx1, tx = getTwoAndTail xl
            let hy0, hy1, ty = getTwoAndTail yl
            let hxo0, hxo1, txo = getTwoAndTail xol
            let hyo0, hyo1, tyo = getTwoAndTail yol
            let col = maxCol ValueType.Solution hxo0 hxo1 hyo0 hyo1
            let s = Shape.init (StyleParam.ShapeType.Line,hx0,hx1,hy0,hy1,Line=(Line.init(Width=2, Color=col)),Opacity=opacity)
            makeLines tx ty txo tyo (s :: shapes)

        let shapes1 = makeLines xlines2 ylines2 xlines1 ylines1 [] 

        let rec makeRects xl yl xol yol shapes =
            let getTwoAndTail l =
                match l with
                | f :: s :: t -> f, s, t
                | _ -> 0., 0., []
            if List.isEmpty xl then shapes
            else
            let hx0, hx1, tx = getTwoAndTail xl
            let hy0, hy1, ty = getTwoAndTail yl
            let hxo0, hxo1, txo = getTwoAndTail xol
            let hyo0, hyo1, tyo = getTwoAndTail yol
            let col = maxCol ValueType.Solution hxo0 hxo1 hyo0 hyo1
            let s = Shape.init (StyleParam.ShapeType.Rectangle,hx0,hx1,hy0,hy1,Line=(Line.init(Width=0)),Opacity=opacity,Fillcolor=col)
            makeRects tx ty txo tyo (s :: shapes)

        let shapes2 = makeRects xrects2 yrects2 xrects1 yrects1 shapes1 

        let c =
            [
                Chart.Point(inxs1,inys1,Name="inexact")
                |> Chart.withMarkerStyle(Size=5,Color=colForValtype ValueType.Solution,Opacity=opacity)
                |> Chart.withSize(1024.,768.)
                Chart.Point(xs2,ys2,Name="exact")
                |> Chart.withMarkerStyle(Size=5,Color=colForValtype ValueType.Solution)
                //|> Chart.withY_AxisStyle StyleParam.AxisType.Log
                |> Chart.withShapes shapes2;
            ] 
            |> Chart.Combine
        let c1 = if title.IsSome then c |> Chart.withTitle(title.Value) else c
        c1 |> Chart.Show
        ()

    let plotCurve (expr : uint64 -> UboundExpression) (icr:IFrom<_>) minpower (ubg0:Uboundg<'F>) (ubg1:Uboundg<'F>) (title : string option) =
        let env = ubg0.Env
        let ifl = env.ifl

        let nextX (x:Uboundg<'F>) =
            let u = fstBound x.Ubound.Value
            let nu = nborhi env u minpower
            icr.fromu nu,(expr u).EvalUBG icr

        let _, _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            fWhile
                (fun (x,y, xs, ys, inxs, inys, xlines, ylines, xrects, yrects) -> x .< ubg1 )
                (fun (x,y, xs, ys, inxs, inys, xlines, ylines, xrects, yrects) ->
                    let x_, y_ = nextX x
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x.G y_.G ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    x_, y_, xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_
                ) (ubg0, icr.from 0., [], [], [], [], [], [], [], [])
        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 title

    let plotCurveTest (pred : uint64 -> UboundExpressionBool) (exprtrue : uint64 -> UboundExpression) (exprfalse : uint64 -> UboundExpression) (icr:IFrom<_>) minpower (ubg0:Uboundg<'F>) (ubg1:Uboundg<'F>) (title : string option) =
        let env = ubg0.Env
        let ifl = env.ifl

        let nextX (x:Uboundg<'F>) =
            let u = fstBound x.Ubound.Value
            let nu = nborhi env u minpower
            // passing y value in unum and back to take into account the actual precision
            let y = if (pred u).TestUBG icr then (exprtrue u).EvalUBG icr else (exprfalse u).EvalUBG icr
            let yu = y.Ubound.Value
            icr.fromu nu, icr.fromub yu

        let _, _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            fWhile
                (fun (x,y, xs, ys, inxs, inys, xlines, ylines, xrects, yrects) -> x .< ubg1 )
                (fun (x,y, xs, ys, inxs, inys, xlines, ylines, xrects, yrects) ->
                    let x_, y_ = nextX x
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x.G y_.G ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    x_, y_, xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_
                ) (ubg0, icr.from 0., [], [], [], [], [], [], [], [])

        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 title

    let plotCurveTestb (pred : uint64 -> UboundExpressionBool) (exprtrue : uint64 -> UboundExpression) (exprfalse : uint64 -> UboundExpression) (icr:IFrom<_>) minpower (ub0:Ubound<'F>) (ub1:Ubound<'F>) (title : string option) =
        let env = ub0.Env
        let ifl = env.ifl

        let nextX (x:Ubound<'F>) =
            let u = fstBound x.ubound
            let nu = nborhi env u minpower
            icr.fromu nu, if (pred u).TestUB icr then (exprtrue u).EvalUB icr else (exprfalse u).EvalUB icr

        let _, _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            fWhile
                (fun (x,y, xs, ys, inxs, inys, xlines, ylines, xrects, yrects) -> x .< ub1 )
                (fun (x,y, xs, ys, inxs, inys, xlines, ylines, xrects, yrects) ->
                    let x_, y_ = nextX x
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x.G.Value y_.G.Value ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    x_, y_, xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_
                ) (ub0, icr.from 0., [], [], [], [], [], [], [], [])

        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 title

    let plotPoly env coeffsg minpower f0 f1 =
        let u0 = x2u env f0
        let u1 = x2u env f1
        let ub = Bounds (u0, u1)
        let ubl = uboxlist env ub minpower

        let xys = ubl |> List.map
                        (fun x ->
                            let g = unum2g_nc env x
                            g, polyg env coeffsg g)
        let _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            let rec fw xys_ xs ys inxs inys xlines ylines xrects yrects =
                match xys_ with
                    | h :: t -> 
                    let x_, y_ = h
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x_ y_ ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    fw t xs_ ys_ inxs_ inys_ xlines_ ylines_ xrects_ yrects_
                    | _ -> [], xs, ys, inxs, inys, xlines, ylines, xrects, yrects
            fw xys [] [] [] [] [] [] [] []

        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1

    let fctexact ifl (fct: FloatExpression<'F> -> FloatExpression<'F>) x =
        ( fct (FloatExpression.Expr (Val x)) ).Eval ifl

    let fctinexact ifl (fct: FloatExpression<'F> -> FloatExpression<'F>)  xg =
        let fs x0 x = fct (FloatExpression.Expr (Val x + Val x0))
        let eval (f : 'F -> FloatExpression<'F>) x0 g =
            let g0 = (x0, x0), (Closed, Closed)
            let m = minusg ifl g g0
            let r0 = (f (leftFloat m)).Eval ifl
            let r1 = (f (rightFloat m)).Eval ifl
            let res = if r0 = r1 then (r0, r0), (Closed, Closed)
                         elif r0 < r1 then (r0, r1), (leftInterval m, rightInterval m)
                         else (r1, r0), (rightInterval m, leftInterval m)
            res
        let (xlo, xhi), _ = xg
        let fslo = fs xlo
        let fshi = fs xhi
        let atlo = eval fslo xlo xg
        let athi = eval fshi xhi xg
        intersectg ifl ( atlo )
                       ( athi )

    // function evaluation of a general interval without u-layer information loss.
    let fctevalg env (fct: FloatExpression<'F> -> FloatExpression<'F>) xg =
        let ifl = env.ifl
        if gQ ifl xg then
            let (xgL, xgR), (xgLb, xgRb) = xg
            if ifl.IsNaN xgL || ifl.IsNaN  xgR then (ifl.NaN, ifl.NaN), (Open, Open)
            elif xgL = xgR then let fxgL = fctexact ifl fct xgL in (fxgL, fxgL), (Closed, Closed)
            else
            let fxgL = fctexact ifl fct xgL
            let gL = ((fxgL,fxgL),(Closed,Closed))
            let gL1 = if xgLb then (fst gL),(Open,Open) else gL
            let fxgR = fctexact ifl fct xgR
            let gR = ((fxgR,fxgR),(Closed,Closed))
            let gR1 = if xgRb then (fst gR),(Open,Open) else gR
            let (gLL,gLR),(gLLb,gLRb) = gL1
            let (gRL,gRR),(gRLb,gRRb) = gR1
            let minLSide = gLL < gRL || (gLL = gRL && not gLLb)
            let min_, minQ = if minLSide then gLL, gLLb else gRL, gRLb
            let maxLSide = gLR > gRR || (gLR = gRR && not gLRb)
            let max_, maxQ = if maxLSide then gLR, gLRb else gRR, gRRb
            let trials_ = [xg]
            let M_ = ((min_,max_),(minQ,maxQ))
            let M1, _ = fWhile ( fun (M, (trials:_ list)) -> trials.Length >= 1 )
                            ( fun (M, trials) ->
                            let pg = fctinexact ifl fct (List.head trials)

                            let pgu = g2u env pg
                            let pg1 = ubound2g_nc env pgu

                            let Mu = g2u env M
                            let M1 = ubound2g_nc env Mu

                            let intersec = intersectg ifl pg1 M1
                            if samegQ ifl intersec pg1 then
                                M1, List.tail trials
                            else
                                let b = bisect env (List.head trials)
                                let trials1 = b.[0] :: b.[1] :: (List.tail trials)
                                let (tr0L, tr0R), _ = List.head trials1
                                let ftr0R = fctexact ifl fct tr0R
                                let gM = (ftr0R,ftr0R),(Closed,Closed)
                                let (gML, gMR), (gMLb, gMRb) = gM
                                let (mint_,maxt_),(mintQ,maxtQ) = M1
                                let mint1, mint1Q = if gML < mint_ || (gML = mint_ && not gMLb) then gML, gMLb else mint_, mintQ
                                let maxt1, maxt1Q = if gMR > maxt_ || (gMR = maxt_ && not gMRb) then gMR, gMRb else maxt_, maxtQ
                                ((mint1,maxt1),(mint1Q,maxt1Q)), trials1
                            ) (M_, trials_)
            M1
        else (ifl.NaN, ifl.NaN), (Open, Open)

    let plotFct env fct minpower f0 f1 (title : string option) =
        let u0 = x2u env f0
        let u1 = x2u env f1
        let ub = Bounds (u0, u1)
        let ubl = uboxlist env ub minpower
        let xys = ubl |> List.map
                        (fun x ->
                            let g = unum2g_nc env x
                            g, fctevalg env fct g)
        let _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            let rec fw xys_ xs ys inxs inys xlines ylines xrects yrects =
                match xys_ with
                    | h :: t -> 
                    let x_, y_ = h
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x_ y_ ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    fw t xs_ ys_ inxs_ inys_ xlines_ ylines_ xrects_ yrects_
                    | _ -> [], xs, ys, inxs, inys, xlines, ylines, xrects, yrects
            fw xys [] [] [] [] [] [] [] []
        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 title

    let fcttestexact ifl (predfct: FloatExpression<'F> -> FloatExpressionBool<'F>) (fcttrue: FloatExpression<'F> -> FloatExpression<'F>) (fctfalse: FloatExpression<'F> -> FloatExpression<'F>) x =
        let res = if (predfct (FloatExpression.Expr (Val x))).Test ifl then
                    (fcttrue (FloatExpression.Expr (Val x))).Eval ifl
                  else
                    (fctfalse (FloatExpression.Expr (Val x))).Eval ifl
        res

    let fcttestinex ifl (predfct: FloatExpression<'F> -> FloatExpressionBool<'F>) (fcttrue: FloatExpression<'F> -> FloatExpression<'F>) (fctfalse: FloatExpression<'F> -> FloatExpression<'F>) x0 x =
        let res = if (predfct (FloatExpression.Expr (Val x + Val x0))).Test ifl then
                    (fcttrue (FloatExpression.Expr (Val x + Val x0))).Eval ifl
                  else
                    (fctfalse (FloatExpression.Expr (Val x + Val x0))).Eval ifl
        res

    let fctinexacttest ifl predfct fcttrue fctfalse 
                       xg =
        let fctinexactx0 x0 = fcttestinex ifl predfct fcttrue fctfalse x0
        let eval f0 x0_ x_ =
            let g0 = (x0_, x0_), (Closed, Closed)
            let m = minusg ifl xg g0
            let r0 = f0 (leftFloat m)
            let r1 = f0 (rightFloat m)
            let res = if r0 = r1 then (r0, r0), (Closed, Closed)
                         elif r0 < r1 then (r0, r1), (leftInterval m, rightInterval m)
                         else (r1, r0), (rightInterval m, leftInterval m)
            res
        let (xlo, xhi), _ = xg
        let finlo = fctinexactx0 xlo
        let finhi = fctinexactx0 xhi
        let atlo = eval finlo xlo xg
        let athi = eval finhi xhi xg
        intersectg ifl ( atlo )
                       ( athi )

    // function evaluation of a general interval without u-layer information loss.
    let fctevaltestg env 
                 (predfct: FloatExpression<'F> -> FloatExpressionBool<'F>) (fcttrue: FloatExpression<'F> -> FloatExpression<'F>) (fctfalse: FloatExpression<'F> -> FloatExpression<'F>)
                 xg =
        let ifl = env.ifl
        if gQ ifl xg then
            let (xgL, xgR), (xgLb, xgRb) = xg
            if ifl.IsNaN xgL || ifl.IsNaN  xgR then (ifl.NaN, ifl.NaN), (Open, Open)
            elif xgL = xgR then
                let fxgL = fcttestexact ifl predfct fcttrue fctfalse xgL
                (fxgL, fxgL), (Closed, Closed)
            else
            let fxgL = fcttestexact ifl predfct fcttrue fctfalse xgL
            let gL = ((fxgL,fxgL),(Closed,Closed))
            let gL1 = if xgLb then (fst gL),(Open,Open) else gL
            let fxgR = fcttestexact ifl predfct fcttrue fctfalse xgR
            let gR = ((fxgR,fxgR),(Closed,Closed))
            let gR1 = if xgRb then (fst gR),(Open,Open) else gR
            let (gLL,gLR),(gLLb,gLRb) = gL1
            let (gRL,gRR),(gRLb,gRRb) = gR1
            let minLSide = gLL < gRL || (gLL = gRL && not gLLb)
            let min_, minQ = if minLSide then gLL, gLLb else gRL, gRLb
            let maxLSide = gLR > gRR || (gLR = gRR && not gLRb)
            let max_, maxQ = if maxLSide then gLR, gLRb else gRR, gRRb
            let trials_ = [xg]
            let M0_ = ((min_,max_),(minQ,maxQ))
            let Mu_ = g2u env M0_
            let M_ = ubound2g_nc env Mu_
            let M1, _ = fWhile ( fun (M, (trials:_ list)) -> trials.Length >= 1 )
                            ( fun (M, trials) ->
                            let pg = fctinexacttest ifl predfct fcttrue fctfalse (List.head trials)
                            let pgu = g2u env pg
                            let pg1 = ubound2g_nc env pgu
                            let intersec = intersectg ifl pg1 M
                            if samegQ ifl intersec pg1 then
                                M, List.tail trials
                            else
                                let b = bisect env (List.head trials)
                                let trials1 = b.[0] :: b.[1] :: (List.tail trials)
                                let (tr0L, tr0R), _ = List.head trials1
                                let ftr0R = fcttestexact ifl predfct fcttrue fctfalse tr0R
                                let gM = (ftr0R,ftr0R),(Closed,Closed)
                                let (gML, gMR), (gMLb, gMRb) = gM
                                let (mint_,maxt_),(mintQ,maxtQ) = M
                                let mint1, mint1Q = if gML < mint_ || (gML = mint_ && not gMLb) then gML, gMLb else mint_, mintQ
                                let maxt1, maxt1Q = if gMR > maxt_ || (gMR = maxt_ && not gMRb) then gMR, gMRb else maxt_, maxtQ
                                let M0 = ((mint1,maxt1),(mint1Q,maxt1Q))
                                let Mu = g2u env M0
                                let M1 = ubound2g_nc env Mu
                                M1, trials1
                            ) (M_, trials_)
            M1
        else (ifl.NaN, ifl.NaN), (Open, Open)

    let plotFctTest env predfct fcttrue fctfalse minpower f0 f1 (title : string option) =

        let u0 = x2u env f0
        let u1 = x2u env f1
        let ub = Bounds (u0, u1)
        let ubl = uboxlist env ub minpower

        let xys = ubl |> List.map
                        (fun x ->
                            let g = unum2g_nc env x
                            g, fctevaltestg env predfct fcttrue fctfalse g)

        let _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            let rec fw xys_ xs ys inxs inys xlines ylines xrects yrects =
                match xys_ with
                    | h :: t -> 
                    let x_, y_ = h
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x_ y_ ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    fw t xs_ ys_ inxs_ inys_ xlines_ ylines_ xrects_ yrects_
                    | _ -> [], xs, ys, inxs, inys, xlines, ylines, xrects, yrects
            fw xys [] [] [] [] [] [] [] []


        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 title

    let fctexactubg env (fct: UboundExpression -> UboundExpression) icr x  =
        let u = x2u env x
        ( fct (Expr (FromU u)) ).EvalUBG icr

    let fctinexactubg env (fct: UboundExpression -> UboundExpression) icr xg =
        let ifl = env.ifl
        let fs x0 x =
            let u0 = x2u env x0
            let u = x2u env x
            fct (Expr (FromU u + FromU u0))
        let eval (f:'F -> UboundExpression) x0 g =
            let g0 = (x0, x0), (Closed, Closed)
            let m = minusg ifl g g0
            let r0 = leftFloat ( (f (leftFloat m) ).EvalUBG icr ).G
            let r1 = leftFloat ( (f (rightFloat m) ).EvalUBG icr ).G
            let res = if r0 = r1 then (r0, r0), (Closed, Closed)
                         elif r0 < r1 then (r0, r1), (leftInterval m, rightInterval m)
                         else (r1, r0), (rightInterval m, leftInterval m)
            res
        let (xlo, xhi), _ = xg
        let fslo = fs xlo
        let fshi = fs xhi
        let atlo = eval fslo xlo xg
        let athi = eval fshi xhi xg
        intersectg ifl ( atlo )
                       ( athi )

    // function evaluation of a general interval without u-layer information loss.
    let fctevalubg env (fct: UboundExpression -> UboundExpression) icr xg =
        let ifl = env.ifl
        if gQ ifl xg then
            let (xgL, xgR), (xgLb, xgRb) = xg
            if ifl.IsNaN xgL || ifl.IsNaN  xgR then (ifl.NaN, ifl.NaN), (Open, Open)
            elif xgL = xgR then (fctexactubg env fct icr xgL).G
            else
            let fxgL = leftFloat (fctexactubg env fct icr xgL).G
            let gL = ((fxgL,fxgL),(Closed,Closed))
            let gL1 = if xgLb then (fst gL),(Open,Open) else gL
            let fxgR = leftFloat (fctexactubg env fct icr xgR).G
            let gR = ((fxgR,fxgR),(Closed,Closed))
            let gR1 = if xgRb then (fst gR),(Open,Open) else gR
            let (gLL,gLR),(gLLb,gLRb) = gL1
            let (gRL,gRR),(gRLb,gRRb) = gR1
            let minLSide = gLL < gRL || (gLL = gRL && not gLLb)
            let min_, minQ = if minLSide then gLL, gLLb else gRL, gRLb
            let maxLSide = gLR > gRR || (gLR = gRR && not gLRb)
            let max_, maxQ = if maxLSide then gLR, gLRb else gRR, gRRb
            let trials_ = [xg]
            let M0_ = ((min_,max_),(minQ,maxQ))
            let Mu_ = g2u env M0_
            let M_ = ubound2g_nc env Mu_
            let M1, _ = fWhile ( fun (M, (trials:_ list)) -> trials.Length >= 1 )
                            ( fun (M, trials) ->
                            let pg = fctinexactubg env fct icr (List.head trials)

                            let pgu = g2u env pg
                            let pg1 = ubound2g_nc env pgu
                            let intersec = intersectg ifl pg1 M
                            if samegQ ifl intersec pg1 then
                                M, List.tail trials
                            else
                                let b = bisect env (List.head trials)
                                let trials1 = b.[0] :: b.[1] :: (List.tail trials)
                                let (tr0L, tr0R), _ = List.head trials1
                                let ftr0R = leftFloat (fctexactubg env fct icr tr0R).G
                                let gM = (ftr0R,ftr0R),(Closed,Closed)
                                let (gML, gMR), (gMLb, gMRb) = gM
                                let (mint_,maxt_),(mintQ,maxtQ) = M
                                let mint1, mint1Q = if gML < mint_ || (gML = mint_ && not gMLb) then gML, gMLb else mint_, mintQ
                                let maxt1, maxt1Q = if gMR > maxt_ || (gMR = maxt_ && not gMRb) then gMR, gMRb else maxt_, maxtQ
                                let M0 = ((mint1,maxt1),(mint1Q,maxt1Q))
                                let Mu = g2u env M0
                                let M1 = ubound2g_nc env Mu
                                M1, trials1
                            ) (M_, trials_)
            M1
        else (ifl.NaN, ifl.NaN), (Open, Open)

    let plotFctUBG (fct : UboundExpression -> UboundExpression) (icr:IFrom<_>) minpower (ubg0:Uboundg<'F>) (ubg1:Uboundg<'F>) (title : string option) =
        let env = ubg0.Env
        let ifl = env.ifl
        let u0 = fstBound ubg0.Ubound.Value
        let u1 = fstBound ubg1.Ubound.Value
        let ub = Bounds (u0, u1)
        let ubl = uboxlist env ub minpower
        let xys = ubl |> List.map
                        (fun x ->
                            let g = unum2g_nc env x
                            let ubres = (fct (Expr (FromU x)) ).EvalUBG icr
                            let (urL, urR), _ = ubres.G
                            if ifl.IsInf urL || ifl.IsInf urR then
                                g,  ubres.G
                            else
                                g, fctevalubg env fct icr g)
        let _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            let rec fw xys_ xs ys inxs inys xlines ylines xrects yrects =
                match xys_ with
                    | h :: t -> 
                    let x_, y_ = h
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x_ y_ ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    fw t xs_ ys_ inxs_ inys_ xlines_ ylines_ xrects_ yrects_
                    | _ -> [], xs, ys, inxs, inys, xlines, ylines, xrects, yrects
            fw xys [] [] [] [] [] [] [] []
        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 title

    let fcttestu (predfct: UboundExpression -> UboundExpressionBool) (fcttrue: UboundExpression -> UboundExpression) (fctfalse: UboundExpression -> UboundExpression) icr u =
        let res =
            if (predfct (Expr (FromU u))).TestUBG icr then
                (fcttrue (Expr (FromU u))).EvalUBG icr
            else
                (fctfalse (Expr (FromU u))).EvalUBG icr
        res

    let fcttestexactubg env (predfct: UboundExpression -> UboundExpressionBool) (fcttrue: UboundExpression -> UboundExpression) (fctfalse: UboundExpression -> UboundExpression) icr x =
        let u = x2u env x
        let res = fcttestu predfct fcttrue fctfalse icr u
        res

    let fcttestinexactubg env (predfct: UboundExpression -> UboundExpressionBool) (fcttrue: UboundExpression -> UboundExpression) (fctfalse: UboundExpression -> UboundExpression) icr xg =
        let ifl = env.ifl

        let fs x0 x =
            let u0 = x2u env x0
            let u = x2u env x
            if (predfct (Expr (FromU u + FromU u0))).TestUBG icr then
                (fcttrue(Expr (FromU u + FromU u0))).EvalUBG icr
            else
                (fctfalse(Expr (FromU u + FromU u0))).EvalUBG icr

        let eval (f: 'F -> Uboundg<'F>) x0 g =
            let g0 = (x0, x0), (Closed, Closed)
            let m = minusg ifl xg g0
            let lf = leftFloat m
            let r0 = leftFloat (f lf).G
            let rf = rightFloat m
            let r1 = leftFloat (f rf).G
            let res = if r0 = r1 then (r0, r0), (Closed, Closed)
                         elif r0 < r1 then (r0, r1), (leftInterval m, rightInterval m)
                         else (r1, r0), (rightInterval m, leftInterval m)
            res
        let (xlo, xhi), _ = xg
        let finlo = fs xlo
        let finhi = fs xhi
        let atlo = eval finlo xlo xg
        let athi = eval finhi xhi xg
        intersectg ifl ( atlo )
                       ( athi )

    // function evaluation of a general interval without u-layer information loss.
    let fcttestevalubg env 
                 (predfct: UboundExpression -> UboundExpressionBool) (fcttrue: UboundExpression -> UboundExpression) (fctfalse: UboundExpression -> UboundExpression)
                 icr xg =
        let ifl = env.ifl
        if gQ ifl xg then
            let (xgL, xgR), (xgLb, xgRb) = xg
            if ifl.IsNaN xgL || ifl.IsNaN  xgR then (ifl.NaN, ifl.NaN), (Open, Open)
            elif xgL = xgR then
                let fxgL = leftFloat (fcttestexactubg env predfct fcttrue fctfalse icr xgL ).G
                (fxgL, fxgL), (Closed, Closed)
            else
            let fxgL = leftFloat (fcttestexactubg env predfct fcttrue fctfalse icr xgL).G
            let gL = ((fxgL,fxgL),(Closed,Closed))
            let gL1 = if xgLb then (fst gL),(Open,Open) else gL
            let fxgR = leftFloat (fcttestexactubg env predfct fcttrue fctfalse icr xgR).G
            let gR = ((fxgR,fxgR),(Closed,Closed))
            let gR1 = if xgRb then (fst gR),(Open,Open) else gR
            let (gLL,gLR),(gLLb,gLRb) = gL1
            let (gRL,gRR),(gRLb,gRRb) = gR1
            let minLSide = gLL < gRL || (gLL = gRL && not gLLb)
            let min_, minQ = if minLSide then gLL, gLLb else gRL, gRLb
            let maxLSide = gLR > gRR || (gLR = gRR && not gLRb)
            let max_, maxQ = if maxLSide then gLR, gLRb else gRR, gRRb
            let trials_ = [xg]
            let M0_ = ((min_,max_),(minQ,maxQ))
            let Mu_ = g2u env M0_
            let M_ = ubound2g_nc env Mu_
            let M1, _ = fWhile ( fun (M, (trials:_ list)) -> trials.Length >= 1 )
                            ( fun (M, trials) ->
                            let pg = fcttestinexactubg env predfct fcttrue fctfalse icr (List.head trials)

                            let pgu = g2u env pg
                            let pg1 = ubound2g_nc env pgu

                            let intersec = intersectg ifl pg1 M
                            if samegQ ifl intersec pg1 then
                                M, List.tail trials
                            else
                                let b = bisect env (List.head trials)
                                let trials1 = b.[0] :: b.[1] :: (List.tail trials)
                                let (tr0L, tr0R), _ = List.head trials1
                                let ftr0R = leftFloat (fcttestexactubg env predfct fcttrue fctfalse icr tr0R).G
                                let gM = (ftr0R,ftr0R),(Closed,Closed)
                                let (gML, gMR), (gMLb, gMRb) = gM
                                let (mint_,maxt_),(mintQ,maxtQ) = M
                                let mint1, mint1Q = if gML < mint_ || (gML = mint_ && not gMLb) then gML, gMLb else mint_, mintQ
                                let maxt1, maxt1Q = if gMR > maxt_ || (gMR = maxt_ && not gMRb) then gMR, gMRb else maxt_, maxtQ
                                let M0 = ((mint1,maxt1),(mint1Q,maxt1Q))
                                let Mu = g2u env M0
                                let M1 = ubound2g_nc env Mu
                                M1, trials1
                            ) (M_, trials_)
            M1
        else (ifl.NaN, ifl.NaN), (Open, Open)

    let plotFctTestUBG predfct fcttrue fctfalse minpower icr (ubg0:Uboundg<'F>) (ubg1:Uboundg<'F>) (title : string option) =
        let env = ubg0.Env
        let ifl = env.ifl
        let u0 = fstBound ubg0.Ubound.Value
        let u1 = fstBound ubg1.Ubound.Value
        let ub = Bounds (u0, u1)
        let ubl = uboxlist env ub minpower
        let xys = ubl |> List.map
                        (fun x ->
                            let ubres = fcttestu predfct fcttrue fctfalse icr x
                            let g = unum2g_nc env x
                            let (urL, urR), _ = ubres.G
                            if ifl.IsInf urL || ifl.IsInf urR then
                                g,  ubres.G
                            else
                                let res = fcttestevalubg env predfct fcttrue fctfalse icr g
                                g , res)

        let _, xs1, ys1, inxs1, inys1, xlines1, ylines1, xrects1, yrects1 =
            let rec fw xys_ xs ys inxs inys xlines ylines xrects yrects =
                match xys_ with
                    | h :: t -> 
                    let x_, y_ = h
                    let xs_, ys_, inxs_, inys_, xlines_, ylines_, xrects_, yrects_ = plotg env x_ y_ ValueType.Solution xs ys inxs inys xlines ylines xrects yrects
                    fw t xs_ ys_ inxs_ inys_ xlines_ ylines_ xrects_ yrects_
                    | _ -> [], xs, ys, inxs, inys, xlines, ylines, xrects, yrects
            fw xys [] [] [] [] [] [] [] []


        correctAndPlot xs1 ys1 inxs1 inys1 xlines1 ylines1 xrects1 yrects1 title
