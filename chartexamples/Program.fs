open System
open fsunum

open unum64
open ifl
open uboundenv64

open FSharp.Plotly
open plot

// convenient aliases
type fexp = FloatExpression<float>
type fexpb = FloatExpressionBool<float>

[<EntryPoint>]
let main argv =
    printfn "fsunum charts"

    let env23f = setenv 2 3 SPFloat.IFloat
    let ENV23f = new ENVg<float> (env23f)
    let ifr23f = ENV23f.IFrom

    let c1 = 
            plotFct env23f
                (fun U -> fexp.From 1. + fexp.Sqr( fexp.Expr U ) + fexp.Log( fexp.Abs(fexp.From 1. + fexp.From 3. * (fexp.From 1. - fexp.Expr U)) ) / fexp.From 80. )
                -8. 0.8 2. (Some("Smooth surprise not found sampling in the scratchpad"))
    let c2 =
            plotCurve
                (fun ub -> From 1. + Square( FromU ub ) + Log( Abs(From 1. + From 3. * (From 1. - FromU ub)) ) / From 80. )
                ifr23f -5. (ifr23f.from 0.8) (ifr23f.from 2.) (Some("Smooth surprise found with (nbor) Uboundg"))
    let c3 = 
            plotFctUBG
                (fun U -> From 1. + Square( Expr U ) + Log( Abs(From 1. + From 3. * (From 1. - Expr U)) ) / From 80. )
                ifr23f -5. (ifr23f.from 0.8) (ifr23f.from 2.) (Some("Smooth surprise found with tightest bounds"))

    let c4 = 
            plotFctTest ENV23f.Env
                ( fun X -> fexpb.Equal (fexp.Expr X, fexp.From 0.) )
                ( fun X -> fexp.From 1.)
                ( fun X -> fexp.Sin (fexp.Expr X) / fexp.Expr X )
                -5. -2. 12. (Some("Sinc evaluated in the scratchpad and with sampling"))

    let c5 = 
            plotCurveTest
                ( fun u -> Equal (FromU u, From 0.) )
                ( fun u -> From 1.)
                ( fun u -> (Sin (FromU u * From 180. / From Math.PI) / FromU u ) )
                ifr23f -5. (ifr23f.from -2.) (ifr23f.from 12.) (Some("Sinc with (nbor) Uboundg"))

    let c6 = 
            plotFctTestUBG
                ( fun X -> Equal (Expr X, From 0.) )
                ( fun X -> From 1.)
                ( fun X -> (Sin (Expr X * From 180. / From Math.PI) / Expr X ) )
                -3. ifr23f (ifr23f.from -2.) (ifr23f.from 12.) (Some("Sinc not bounded in the general Uboundg case"))

    let c7 = 
            plotFctTestUBG
                ( fun X -> Equal (Expr X, From 0.) )
                ( fun X -> From 1.)
                ( fun X -> LowPass ( (From 1.), (HighPass ( (From -1.), (Sin (Expr X * From 180. / From Math.PI) / Expr X )))) )
                -3. ifr23f (ifr23f.from -2.) (ifr23f.from 12.) (Some("Sinc bounded in [-1, 1] in the general Uboundg case"))


    0 // return an integer exit code
