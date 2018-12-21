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

(*
    Notes:
    Types that encapsulate the unum64 environment and functions (from unum64.fs), setting a simple syntax for computations (arithmetic operators and math functions).
    - UboundDM (DM for data moved tallying) and Ubound types encapsulate a ubound and its environment.
    - this environments are defined as interfaces. This allow to have the operators/functions code only in one place.
    - Ubound doesn't tally data movement and has a G lazy member, ensuring the scratchpad (float) value is only evaluate as needed and once per instance.
*)

namespace fsunum


module uboundenv64 =
    open System
    open ifl
    open df
    open unum64

    type IEnvironmentDM<'F> =
        abstract Env : env<'F>
        abstract DataMoved : datamoved option with get,set

    type UboundDM<'E,'F when 'E :> IEnvironmentDM<'F> and 'E : not struct and 'F : comparison> (environment : 'E, ub) =
        // utils
        static let getResUpdateDM (lhsEnvironment : 'E) (dm' : datamoved option, res : ubound)  =
            // ensure Environment changes one at a time 
            lock lhsEnvironment.DataMoved ( fun () ->
                    lhsEnvironment.DataMoved <- match lhsEnvironment.DataMoved, dm' with 
                                                | Some d1, Some d2 -> Some { ubitsmoved = d1.ubitsmoved + d2.ubitsmoved; numbersmoved = d1.numbersmoved + d2.numbersmoved }
                                                | Some d1, None -> Some d1
                                                | None, _ -> None
                )
            new UboundDM<'E,'F> (lhsEnvironment, res)
        static let toUboundList l = List.map (fun (u: UboundDM<'E,'F>) -> u.ubound) l
        static let toUboundTupleArray l = Array.map (fun (u: UboundDM<'E,'F>, v:UboundDM<'E,'F>) -> (u.ubound,v.ubound)) l
        static let toUboundDMTupleArray (env : 'E) (dm' : datamoved option, l : (ubound*ubound) []) =
            let dmn = match env.DataMoved, dm' with
                      | Some(d1), Some(d2) -> Some { ubitsmoved = d1.ubitsmoved + d2.ubitsmoved; numbersmoved = d1.numbersmoved + d2.numbersmoved }
                      | _ -> None
            if dmn.IsSome then env.DataMoved <- Some (env.DataMoved.Value + dmn.Value)
            Array.map (fun (u, v) -> (new UboundDM<'E,'F>(env, u), new UboundDM<'E,'F>(env, v))) l
        // inner data
        member this.Environment = environment
        member this.ubound = ub
        member this.G : Lazy<('F*'F)*(bool*bool)> = lazy (ubound2g_nc environment.Env ub)
        // math operators and functions
        static member (.<) (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F>) = ltuQ lhs.Environment.Env lhs.ubound rhs.ubound
        static member (.>) (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F>) = gtuQ lhs.Environment.Env lhs.ubound rhs.ubound
        static member (.=) (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F> ) = nnequQ lhs.Environment.Env lhs.ubound rhs.ubound
        static member (+) (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F>) = getResUpdateDM lhs.Environment (plusu lhs.Environment.Env (Some datamoved.Zero) lhs.ubound rhs.ubound)
        static member (~-) (u : UboundDM<'E,'F>) = new UboundDM<'E,'F> ( u.Environment, negateu u.Environment.Env u.ubound )
        static member (-) (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F>) = getResUpdateDM lhs.Environment (minusu lhs.Environment.Env (Some datamoved.Zero) lhs.ubound rhs.ubound)
        static member (*) (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F>) = getResUpdateDM lhs.Environment (timesu lhs.Environment.Env (Some datamoved.Zero) lhs.ubound rhs.ubound)
        static member (/) (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F>) = getResUpdateDM lhs.Environment (divideu lhs.Environment.Env (Some datamoved.Zero) lhs.ubound rhs.ubound)
        static member square (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (squareu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member sqrt (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (sqrtu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member Pow (lhs : UboundDM<'E,'F>, rhs : UboundDM<'E,'F>) = getResUpdateDM lhs.Environment (powu lhs.Environment.Env (Some datamoved.Zero) lhs.ubound rhs.ubound)
        static member exp (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (expu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member abs (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (absu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member log (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (logu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member cos (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (cosu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member sin (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (sinu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member cot (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (cotu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member tan (u : UboundDM<'E,'F>) = getResUpdateDM u.Environment (tanu u.Environment.Env (Some datamoved.Zero) u.ubound)
        static member fma (u : UboundDM<'E,'F>) (v : UboundDM<'E,'F>) (w : UboundDM<'E,'F>) = getResUpdateDM u.Environment (fmagu u.Environment.Env (Some datamoved.Zero) u.ubound v.ubound w.ubound)
        static member fdot (al : UboundDM<'E,'F> list) (bl : UboundDM<'E,'F> list) = getResUpdateDM (List.head al).Environment (fdotu (List.head al).Environment.Env (Some datamoved.Zero) (toUboundList al) (toUboundList bl))
        static member improd (a : UboundDM<'E,'F>, b : UboundDM<'E,'F>) (c : UboundDM<'E,'F>, d : UboundDM<'E,'F>) = getResUpdateDM a.Environment (improdu a.Environment.Env (Some datamoved.Zero) (a.ubound, b.ubound) (c.ubound, d.ubound))
        static member realprod (a : UboundDM<'E,'F>, b : UboundDM<'E,'F>) (c : UboundDM<'E,'F>, d : UboundDM<'E,'F>) = getResUpdateDM a.Environment (realprodu a.Environment.Env (Some datamoved.Zero) (a.ubound, b.ubound) (c.ubound, d.ubound))
        static member fsum (al : UboundDM<'E,'F> list) = getResUpdateDM (List.head al).Environment (fsumu (List.head al).Environment.Env (Some datamoved.Zero) (toUboundList al))
        static member fprod (al : UboundDM<'E,'F> list) = getResUpdateDM (List.head al).Environment (fprodu (List.head al).Environment.Env (Some datamoved.Zero) (toUboundList al))
        static member fam (u : UboundDM<'E,'F>) (v : UboundDM<'E,'F>) (w : UboundDM<'E,'F>) = getResUpdateDM u.Environment (famu u.Environment.Env (Some datamoved.Zero) u.ubound v.ubound w.ubound)
        static member fprodratio (numl : UboundDM<'E,'F> list) (denoml : UboundDM<'E,'F> list) = getResUpdateDM (List.head numl).Environment (fprodratiou (List.head numl).Environment.Env (Some datamoved.Zero) (toUboundList numl) (toUboundList denoml))
        static member poly (coeffs : UboundDM<'E,'F> list) (u : UboundDM<'E,'F>) = new UboundDM<'E,'F>( u.Environment, polyu u.Environment.Env (toUboundList coeffs) u.ubound )
        static member cfft (rr : (UboundDM<'E,'F>*UboundDM<'E,'F>) []) n iflg =
            let env = (fst rr.[0]).Environment
            toUboundDMTupleArray env ( cfftu env.Env (toUboundTupleArray rr) n iflg )
        // print value as a Unuml/Ubound
        member this.ViewUnum = viewUB this.Environment.Env ub
        // ToString
        override this.ToString() = view this.Environment.Env this.G.Value

    type IFrom<'U> =
        abstract member from : float -> 'U
        abstract member fromu : uint64 -> 'U
        abstract member fromub : ubound -> 'U

            //static let mutable dm = Some {ubitsmoved = 0; numbersmoved = 0}
    type ENVDM<'F when 'F: comparison > (env : env<'F>, dm : datamoved option) =
        let mutable dm_ = dm
        interface IEnvironmentDM<'F> with
            override this.Env = env
            override this.DataMoved with get () = dm_ and set d = dm_ <- d 
        member this.IEnvironmentDM = this :> IEnvironmentDM<_>
        interface IFrom<UboundDM<IEnvironmentDM<'F>,'F>> with
            override this.from x = new UboundDM<_,_>( this.IEnvironmentDM, Unum (x2u env (env.ifl.from x)) )
            override this.fromu x =  new UboundDM<_,_>( this.IEnvironmentDM, Unum x )
            override this.fromub x =  new UboundDM<_,_>( this.IEnvironmentDM, x )
        member this.IFrom = this :> IFrom<_>
        member this.Zero = new UboundDM<_,_>( this.IEnvironmentDM, Unum (env.zerou) )
        member this.One = new UboundDM<_,_>( this.IEnvironmentDM, Unum (env.oneu) )

    type Ubound<'F when 'F: comparison> (env : env<'F>, ub) =
        // utils
        static let fromg ev' g' = new Ubound<'F> ( ev', g2u ev' g')
        static let toGList l = List.map (fun (ub': Ubound<'F>) -> ub'.G.Value ) l
        static let toUboundTupleArray l = Array.map (fun (u: Ubound<'F>, v:Ubound<'F>) -> (u.ubound,v.ubound)) l
        static let toUboundEnvTupleArray env l = Array.map (fun (u, v) -> (new Ubound<'F>(env, u), new Ubound<'F>(env, v))) l
        // inner data
        member this.Env = env
        member this.ubound = ub
        member this.G : Lazy<('F*'F)*(bool*bool)> = lazy (ubound2g_nc env ub)
        // math operators and functions
        static member (.<) (lhs : Ubound<'F>, rhs : Ubound<'F>) = ltgQ lhs.Env.ifl lhs.G.Value rhs.G.Value
        static member (.>) (lhs : Ubound<'F>, rhs : Ubound<'F>) = gtgQ lhs.Env.ifl lhs.G.Value rhs.G.Value
        static member (.=) (lhs : Ubound<'F>, rhs : Ubound<'F> ) = nneqgQ lhs.Env.ifl lhs.G.Value rhs.G.Value
        static member (+) (lhs : Ubound<'F>, rhs : Ubound<'F>) = fromg lhs.Env (plusg lhs.Env.ifl lhs.G.Value rhs.G.Value)
        static member (~-) (u : Ubound<'F>) = fromg u.Env (negateg u.Env.ifl u.G.Value)
        static member (-) (lhs : Ubound<'F>, rhs : Ubound<'F>) = fromg lhs.Env (minusg lhs.Env.ifl lhs.G.Value rhs.G.Value)
        static member (*) (lhs : Ubound<'F>, rhs : Ubound<'F>) = fromg lhs.Env (timesg lhs.Env.ifl lhs.G.Value rhs.G.Value)
        static member (/) (lhs : Ubound<'F>, rhs : Ubound<'F>) = fromg lhs.Env (divideg lhs.Env.ifl lhs.G.Value rhs.G.Value)
        static member lowpass (lhs : Ubound<'F>, rhs : Ubound<'F>) = fromg lhs.Env (lowpassg lhs.Env.ifl lhs.G.Value rhs.G.Value)
        static member highpass (lhs : Ubound<'F>, rhs : Ubound<'F>) = fromg lhs.Env (highpassg lhs.Env.ifl lhs.G.Value rhs.G.Value)
        static member square (u : Ubound<'F>) = fromg u.Env (squareg u.Env.ifl u.G.Value)
        static member sqrt (u : Ubound<'F>) = fromg u.Env (sqrtg u.Env.ifl u.G.Value)
        static member Pow (lhs : Ubound<'F>, rhs : Ubound<'F>) = fromg lhs.Env (powg lhs.Env.ifl lhs.G.Value rhs.G.Value)
        static member exp (u : Ubound<'F>) = fromg u.Env (expg u.Env u.G.Value)
        static member abs (u : Ubound<'F>) = fromg u.Env (absg u.Env.ifl u.G.Value)
        static member log (u : Ubound<'F>) = fromg u.Env (logg u.Env.ifl u.G.Value)
        static member cos (u : Ubound<'F>) = fromg u.Env (cosg u.Env.ifl u.G.Value)
        static member sin (u : Ubound<'F>) = fromg u.Env (sing u.Env.ifl u.G.Value)
        static member cot (u : Ubound<'F>) = fromg u.Env (cotg u.Env.ifl u.G.Value)
        static member tan (u : Ubound<'F>) = fromg u.Env (tang u.Env.ifl u.G.Value)
        static member fma (u : Ubound<'F>) (v : Ubound<'F>) (w : Ubound<'F>) = fromg u.Env (fmag u.Env.ifl u.G.Value v.G.Value w.G.Value)
        static member fdot (al : Ubound<'F> list) (bl : Ubound<'F> list) = fromg (List.head al).Env (fdotg (List.head al).Env.ifl (toGList al) (toGList bl))
        static member improd (a : Ubound<'F>, b : Ubound<'F>) (c : Ubound<'F>, d : Ubound<'F>) = fromg a.Env (improdg a.Env.ifl (a.G.Value, b.G.Value) (c.G.Value, d.G.Value))
        static member realprod (a : Ubound<'F>, b : Ubound<'F>) (c : Ubound<'F>, d : Ubound<'F>) = fromg a.Env (realprodg a.Env.ifl (a.G.Value, b.G.Value) (c.G.Value, d.G.Value))
        static member fsum (al : Ubound<'F> list) = fromg (List.head al).Env (fsumg (List.head al).Env.ifl (toGList al))
        static member fprod (al : Ubound<'F> list) = fromg (List.head al).Env (fprodg (List.head al).Env.ifl (toGList al))
        static member fam (u : Ubound<'F>) (v : Ubound<'F>) (w : Ubound<'F>) = fromg u.Env  (famg u.Env.ifl u.G.Value v.G.Value w.G.Value)
        static member fprodratio (numl : Ubound<'F> list) (denoml : Ubound<'F> list) = fromg (List.head numl).Env (fprodratiog (List.head numl).Env.ifl (toGList numl) (toGList denoml))
        static member poly (coeffs : Ubound<'F> list) (u : Ubound<'F>) = fromg u.Env (polyg u.Env (toGList coeffs) u.G.Value)
        static member cfft (rr : (Ubound<'F>*Ubound<'F>) []) n iflg =
            let env = (fst rr.[0]).Env
            toUboundEnvTupleArray env (snd <| cfftu env (toUboundTupleArray rr) n iflg)
        // print value at a given precision
        member this.ViewAtPrec prec = viewAtPrec this.Env this.G.Value prec
        // print value as a Unuml/Ubound
        member this.ViewUnum = viewUB this.Env ub
        // ToString
        override this.ToString() = view this.Env this.G.Value

     type Uboundg<'F when 'F: comparison> (env : env<'F>, g : ('F*'F)*(bool*bool)) =
        static let toGList l = List.map (fun (ub': Uboundg<'F>) -> ub'.G ) l
        static let toUboundTupleArray l = Array.map (fun (u: Uboundg<'F>, v:Uboundg<'F>) -> (u.Ubound.Value,v.Ubound.Value)) l
        static let toUboundEnvTupleArray env l = Array.map (fun (u, v) -> ( Uboundg<'F> (env, ubound2g_nc env u), Uboundg<'F> (env, ubound2g_nc env v)) ) l
        // inner data
        member this.Env = env
        member this.Ubound : Lazy<ubound> = lazy (g2u env g)
        member this.G = g
        // math operators and functions
        static member (.<) (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = ltgQ lhs.Env.ifl lhs.G rhs.G
        static member (.>) (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = gtgQ lhs.Env.ifl lhs.G rhs.G
        static member (.=) (lhs : Uboundg<'F>, rhs : Uboundg<'F> ) = nneqgQ lhs.Env.ifl lhs.G rhs.G
        static member (+) (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = Uboundg (lhs.Env, (plusg lhs.Env.ifl lhs.G rhs.G))
        static member (~-) (u : Uboundg<'F>) = Uboundg (u.Env, negateg u.Env.ifl u.G)
        static member (-) (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = Uboundg ( lhs.Env, (minusg lhs.Env.ifl lhs.G rhs.G))
        static member (*) (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = Uboundg ( lhs.Env, (timesg lhs.Env.ifl lhs.G rhs.G))
        static member (/) (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = Uboundg ( lhs.Env, (divideg lhs.Env.ifl lhs.G rhs.G))
        static member id (u : Uboundg<'F>) = u
        static member lowpass (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = Uboundg ( lhs.Env, (lowpassg lhs.Env.ifl lhs.G rhs.G))
        static member highpass (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = Uboundg ( lhs.Env, (highpassg lhs.Env.ifl lhs.G rhs.G))
        static member square (u : Uboundg<'F>) = Uboundg ( u.Env, (squareg u.Env.ifl u.G))
        static member sqrt (u : Uboundg<'F>) = Uboundg ( u.Env, (sqrtg u.Env.ifl u.G))
        static member Pow (lhs : Uboundg<'F>, rhs : Uboundg<'F>) = Uboundg ( lhs.Env, (powg lhs.Env.ifl lhs.G rhs.G))
        static member exp (u : Uboundg<'F>) = Uboundg ( u.Env, (expg u.Env u.G))
        static member abs (u : Uboundg<'F>) = Uboundg ( u.Env, (absg u.Env.ifl u.G))
        static member log (u : Uboundg<'F>) = Uboundg ( u.Env, (logg u.Env.ifl u.G))
        static member cos (u : Uboundg<'F>) = Uboundg ( u.Env, (cosg u.Env.ifl u.G))
        static member sin (u : Uboundg<'F>) = Uboundg ( u.Env, (sing u.Env.ifl u.G))
        static member cot (u : Uboundg<'F>) = Uboundg ( u.Env, (cotg u.Env.ifl u.G))
        static member tan (u : Uboundg<'F>) = Uboundg ( u.Env, (tang u.Env.ifl u.G))
        static member fma (u : Uboundg<'F>) (v : Uboundg<'F>) (w : Uboundg<'F>) = Uboundg ( u.Env, (fmag u.Env.ifl u.G v.G w.G))
        static member fdot (al : Uboundg<'F> list) (bl : Uboundg<'F> list) = Uboundg ( (List.head al).Env, (fdotg (List.head al).Env.ifl (toGList al) (toGList bl)))
        static member improd (a : Uboundg<'F>, b : Uboundg<'F>) (c : Uboundg<'F>, d : Uboundg<'F>) = Uboundg ( a.Env, (improdg a.Env.ifl (a.G, b.G) (c.G, d.G)))
        static member realprod (a : Uboundg<'F>, b : Uboundg<'F>) (c : Uboundg<'F>, d : Uboundg<'F>) = Uboundg ( a.Env, (realprodg a.Env.ifl (a.G, b.G) (c.G, d.G)))
        static member fsum (al : Uboundg<'F> list) = Uboundg ( (List.head al).Env, (fsumg (List.head al).Env.ifl (toGList al)))
        static member fprod (al : Uboundg<'F> list) = Uboundg ( (List.head al).Env, (fprodg (List.head al).Env.ifl (toGList al)))
        static member fam (u : Uboundg<'F>) (v : Uboundg<'F>) (w : Uboundg<'F>) = Uboundg ( u.Env, (famg u.Env.ifl u.G v.G w.G))
        static member fprodratio (numl : Uboundg<'F> list) (denoml : Uboundg<'F> list) = Uboundg ( (List.head numl).Env, (fprodratiog (List.head numl).Env.ifl (toGList numl) (toGList denoml)))
        static member poly (coeffs : Uboundg<'F> list) (u : Uboundg<'F>) = Uboundg ( u.Env, (polyg u.Env (toGList coeffs) u.G))
        static member cfft (rr : (Uboundg<'F>*Uboundg<'F>) []) (n:int) (iflg:int) =
            let env = (fst rr.[0]).Env
            toUboundEnvTupleArray env (snd <| cfftu env (toUboundTupleArray rr) n iflg)
        // print value at a given precision
        member this.ViewAtPrec prec = viewAtPrec this.Env g prec
        // print value as a Unuml/Ubound
        member this.ViewUnum = viewUB this.Env this.Ubound.Value
        // ToString
        override this.ToString() = view this.Env this.G

    type ENV<'F when 'F: comparison > (env : env<'F>) =
        member this.Env = env
        interface IFrom<Ubound<'F>> with
            override this.from x =  new Ubound<_>( env, Unum (x2u env (env.ifl.from x)) )
            override this.fromu x =  new Ubound<_>( env, Unum x )
            override this.fromub x =  new Ubound<_>( env, x )
        member this.IFrom = this :> IFrom<_>
        member this.Zero = new Ubound<_>( env, Unum (env.zerou) )
        member this.One = new Ubound<_>( env, Unum (env.oneu) )

    let env23f = setenv 2 3 SPFloat.IFloat
    let ENV23f = new ENV<float> (env23f)
    let env23d= setenv 2 3 SPDFloat.IFloat
    let ENV23d = new ENV<dfloat> (env23d)
    let env34f = setenv 3 4 SPFloat.IFloat
    let ENV34f = new ENV<float> (env34f)
    let env34d= setenv 3 4 SPDFloat.IFloat
    let ENV34d = new ENV<dfloat> (env34d)
    let env46f = setenv 4 6 SPFloat.IFloat
    let ENV46f = new ENV<float> (env46f)
    let env46d= setenv 4 6 SPDFloat.IFloat
    let ENV46d = new ENV<dfloat> (env46d)

    type ENVg<'F when 'F: comparison > (env : env<'F>) =
        member this.Env = env
        interface IFrom<Uboundg<'F>> with
            override this.from x =  new Uboundg<_>( env, f2g env.ifl (env.ifl.from x) )
            override this.fromu x =  new Uboundg<_>( env, unum2g env x )
            override this.fromub x =  new Uboundg<_>( env, ubound2g env  x )
        member this.IFrom = this :> IFrom<_>
        member this.Zero = new Uboundg<_>( env, f2g env.ifl (env.ifl.Zero) )
        member this.One = new Uboundg<_>( env, f2g env.ifl (env.ifl.One) )

    let env22gf = setenv 2 2 SPFloat.IFloat
    let ENV22gf = new ENVg<float> (env22gf)
    let env23gf = setenv 2 3 SPFloat.IFloat
    let ENV23gf = new ENVg<float> (env23gf)
    let env23gd = setenv 2 3 SPDFloat.IFloat
    let ENV23gd = new ENVg<dfloat> (env23gd)
    let env34gf = setenv 3 4 SPFloat.IFloat
    let ENV34gf = new ENVg<float> (env34gf)
    let env34gd = setenv 3 4 SPDFloat.IFloat
    let ENV34gd = new ENVg<dfloat> (env34gd)
    let env35gd = setenv 3 5 SPDFloat.IFloat
    let ENV35gd = new ENVg<dfloat> (env35gd)
    let env46gf = setenv 4 6 SPFloat.IFloat
    let ENV46gf = new ENVg<float> (env46gf)
    let env46gd = setenv 4 6 SPDFloat.IFloat
    let ENV46gd = new ENVg<dfloat> (env46gd)

    type IUboundg<'U> =
        abstract member id : 'U -> 'U
        abstract member lessThan : 'U * 'U -> bool
        abstract member greaterThan : 'U * 'U -> bool
        abstract member equal : 'U * 'U -> bool
        abstract member notNowhereEqual : 'U * 'U -> bool
        abstract member lowpass : 'U * 'U -> 'U
        abstract member highpass : 'U * 'U -> 'U
        abstract member plus : 'U * 'U -> 'U
        abstract member negate : 'U -> 'U
        abstract member minus : 'U * 'U -> 'U
        abstract member times : 'U * 'U -> 'U
        abstract member divides : 'U * 'U -> 'U
        abstract member square : 'U -> 'U
        abstract member sqrt : 'U -> 'U
        abstract member Pow : 'U * 'U  -> 'U
        abstract member exp : 'U -> 'U
        abstract member abs : 'U -> 'U
        abstract member log : 'U -> 'U
        abstract member cos : 'U -> 'U
        abstract member sin : 'U -> 'U
        abstract member cot : 'U -> 'U
        abstract member tan : 'U -> 'U
        abstract member fma : 'U * 'U * 'U -> 'U
        abstract member fdot : 'U list * 'U list -> 'U
        abstract member improd : 'U * 'U * 'U * 'U -> 'U
        abstract member realprod : 'U * 'U * 'U * 'U -> 'U
        abstract member fsum : 'U list -> 'U
        abstract member fprod : 'U list -> 'U
        abstract member fam : 'U * 'U * 'U -> 'U
        abstract member fprodratio : 'U list * 'U list -> 'U
        abstract member poly : 'U list * 'U  -> 'U
        abstract member cfft : ('U * 'U) [] * int * int -> ('U * 'U) []

    type UboundExpression =
        | Expr of UboundExpression
        | From of float
        | FromU of uint64
        | LowPass of UboundExpression * UboundExpression
        | HighPass of UboundExpression * UboundExpression
        | Plus of UboundExpression * UboundExpression
        | Minus of UboundExpression * UboundExpression
        | Times of UboundExpression * UboundExpression
        | Divides of UboundExpression * UboundExpression
        | Power of UboundExpression * UboundExpression
        | Abs of UboundExpression
        | Cos of UboundExpression
        | Exp of UboundExpression
        | Log of UboundExpression
        | Negate of UboundExpression
        | Sin of UboundExpression
        | Square of UboundExpression
        | Sqrt of UboundExpression
        | Tan of UboundExpression
        member this.EvalUBG<'F when 'F: comparison> (icr : IFrom<_>) : Uboundg<'F> =
            let rec evalExp exp =
                match exp with
                    | Expr x  -> evalExp x
                    | From x -> icr.from x
                    | FromU x -> icr.fromu x
                    | LowPass (lhs, rhs) ->
                        let lhsv, rhsv = evalExp lhs, evalExp rhs in Uboundg.lowpass ( lhsv, rhsv )
                    | HighPass (lhs, rhs) ->
                        let lhsv, rhsv = evalExp lhs, evalExp rhs in Uboundg.highpass ( lhsv, rhsv )
                    | Plus (lhs, rhs) ->
                        let lhsv, rhsv = evalExp lhs, evalExp rhs in Uboundg.op_Addition ( lhsv, rhsv )
                    | Minus (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Uboundg.op_Subtraction ( lhsv, rhsv )
                    | Times (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Uboundg.op_Multiply ( lhsv, rhsv )
                    | Divides (lhs, rhs) ->
                        let lhsv, rhsv = evalExp lhs, evalExp rhs in Uboundg.op_Division ( lhsv, rhsv )
                    | Power (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Uboundg.Pow( lhsv, rhsv )
                    | Abs x -> let xv = evalExp x in Uboundg.abs xv
                    | Cos x -> let xv = evalExp x in Uboundg.cos xv
                    | Exp x -> let xv = evalExp x in Uboundg.exp xv
                    | Log x -> let xv = evalExp x in Uboundg.log xv
                    | Negate x -> let xv = evalExp x in Uboundg.op_UnaryNegation xv
                    | Sin x -> let xv = evalExp x in Uboundg.sin xv
                    | Square x -> let xv = evalExp x in Uboundg.square xv
                    | Sqrt x -> let xv = evalExp x in Uboundg.sqrt xv
                    | Tan x -> let xv = evalExp x in Uboundg.tan xv
            evalExp this

        member this.EvalUB<'F when 'F: comparison> (icr : IFrom<_>) : Ubound<'F> = 
            let rec evalExp exp =
                match exp with
                    | Expr x  -> evalExp x
                    | From x -> icr.from x
                    | FromU x -> icr.fromu x
                    | LowPass (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Ubound.lowpass ( lhsv, rhsv )
                    | HighPass (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Ubound.highpass ( lhsv, rhsv )
                    | Plus (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in  Ubound.op_Addition ( lhsv, rhsv )
                    | Minus (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Ubound.op_Subtraction ( lhsv, rhsv )
                    | Times (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Ubound.op_Multiply ( lhsv, rhsv )
                    | Divides (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Ubound.op_Division ( lhsv, rhsv )
                    | Power (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in Ubound.Pow( lhsv, rhsv )
                    | Abs x -> let xv = evalExp x in Ubound.abs xv
                    | Cos x -> let xv = evalExp x in Ubound.cos xv
                    | Exp x -> let xv = evalExp x in Ubound.exp xv
                    | Log x -> let xv = evalExp x in Ubound.log xv
                    | Negate x -> let xv = evalExp x in Ubound.op_UnaryNegation xv
                    | Sin x -> let xv = evalExp x in Ubound.sin xv
                    | Square x -> let xv = evalExp x in Ubound.square xv
                    | Sqrt x -> let xv = evalExp x in Ubound.sqrt xv
                    | Tan x -> let xv = evalExp x in Ubound.tan xv
            evalExp this
        member this.EvalF<'F when 'F: comparison> (ifl : IFloat<_>)  = 
            let rec evalExp exp =
                match exp with
                    | Expr x  -> evalExp x
                    | From x -> ifl.create x
                    | FromU x -> ifl.NaN // uint64 doesn't make sense in the IFloat context
                    | LowPass (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in if lhsv < rhsv then lhsv else rhsv
                    | HighPass (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in if lhsv > rhsv then lhsv else rhsv
                    | Plus (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in  ifl.plus ( lhsv, rhsv )
                    | Minus (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.minus ( lhsv, rhsv )
                    | Times (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.times ( lhsv, rhsv )
                    | Divides (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.divides ( lhsv, rhsv )
                    | Power (lhs, rhs) -> let lhsv, rhsv = evalExp lhs, evalExp rhs in ifl.Pow( lhsv, rhsv )
                    | Abs x -> let xv = evalExp x in ifl.abs xv
                    | Cos x -> let xv = evalExp x in ifl.cos xv
                    | Exp x -> let xv = evalExp x in ifl.exp xv
                    | Log x -> let xv = evalExp x in ifl.log xv
                    | Negate x -> let xv = evalExp x in ifl.negate xv
                    | Sin x -> let xv = evalExp x in ifl.sin xv
                    | Square x -> let xv = evalExp x in ifl.sqr xv
                    | Sqrt x -> let xv = evalExp x in ifl.sqrt xv
                    | Tan x -> let xv = evalExp x in ifl.tan xv
            evalExp this
        
        static member (~-) (x) = Negate (x)
        static member (+) (lhs, rhs) = Plus (lhs, rhs)
        static member (-) (lhs, rhs) = Minus (lhs, rhs)
        static member (*) (lhs, rhs) = Times (lhs, rhs)
        static member (/) (lhs, rhs) = Divides (lhs, rhs)
        static member Pow (lhs, rhs) = Power (lhs, rhs)

    type UboundExpressionBool =
        | Not of UboundExpressionBool
        | And of UboundExpressionBool * UboundExpressionBool
        | Or of UboundExpressionBool * UboundExpressionBool
        | LessThan of  UboundExpression * UboundExpression
        | GreaterThan of  UboundExpression * UboundExpression
        | Equal of  UboundExpression * UboundExpression
        | NotNowhereEqual of  UboundExpression * UboundExpression

        member this.TestUB<'F when 'F: comparison> (icr : IFrom<Ubound<'F>>) : bool =
            let rec testExp exp =
                match exp with
                    | Not x -> not (testExp x)
                    | And (lhs, rhs) -> testExp lhs && testExp rhs
                    | Or (lhs, rhs) -> testExp lhs || testExp rhs
                    | LessThan (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUB icr, rhs.EvalUB icr in  lhsv .< rhsv
                    | GreaterThan (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUB icr, rhs.EvalUB icr in  lhsv .> rhsv
                    | Equal (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUB icr, rhs.EvalUB icr in  lhsv.ubound = rhsv.ubound // warning: works when ubounds are in their shortest form.
                    | NotNowhereEqual (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUB icr, rhs.EvalUB icr in  lhsv .= rhsv
            testExp this

        member this.TestUBG<'F when 'F: comparison> (icr : IFrom<Uboundg<'F>>) : bool =
            let rec testExp exp =
                match exp with
                    | Not x -> not (testExp x)
                    | And (lhs, rhs) -> testExp lhs && testExp rhs
                    | Or (lhs, rhs) -> testExp lhs || testExp rhs
                    | LessThan (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUBG icr, rhs.EvalUBG icr in  lhsv .< rhsv
                    | GreaterThan (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUBG icr, rhs.EvalUBG icr in  lhsv .> rhsv
                    | Equal (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUBG icr, rhs.EvalUBG icr in lhsv.Ubound.Value = rhsv.Ubound.Value // warning: works when ubounds are in their shortest form.
                    | NotNowhereEqual (lhs, rhs) -> let lhsv, rhsv = lhs.EvalUBG icr, rhs.EvalUBG icr in  lhsv .= rhsv
            testExp this

        static member not (lhs) = Not lhs
        static member op_BooleanAnd (lhs , rhs) = And (lhs, rhs)
        static member op_BooleanOr (lhs , rhs) = And (lhs, rhs)
        static member (.<) (lhs , rhs) = LessThan (lhs, rhs)
        static member (.>) (lhs , rhs) = GreaterThan (lhs, rhs)
        static member (.=) (lhs , rhs) = NotNowhereEqual (lhs, rhs)
        static member op_Equals (lhs , rhs) = Equal (lhs, rhs)

    let equaldf (d : (dfloat * dfloat) * (bool * bool)) (f : (float * float) * (bool * bool) ) =
        let (dlo,dhi),(dblo, dbhi) = d
        let (flo,fhi),(fblo, fbhi) = f
        dfloat.float dlo = flo &&
        dfloat.float dhi = fhi &&
        dblo = fblo &&
        dbhi = fbhi

    let ComputeUBG (exp:UboundExpression) precision =
        let icr_23f = ENV23gf.IFrom
        let icr_23d = ENV23gd.IFrom
        let icr_34f = ENV34gf.IFrom
        let icr_34d = ENV34gd.IFrom
        let icr_46f = ENV46gf.IFrom
        let icr_46d = ENV46gd.IFrom
        let ifl_f = SPFloat.IFloat
        let ifl_d = SPDFloat.IFloat
        let rprec = 10. ** (float -precision)

        if precision < 1 || precision > 12 then printfn "Compute: precision out of domain [1..12]";  0,0,"ERR",(icr_23f.from Double.NaN).Ubound.Value
        else
            if precision <= 2 then
                let res23d = exp.EvalUBG icr_23d
                let rw23d = relwidthg ifl_d res23d.G
                let res23f = exp.EvalUBG icr_23f
                let rw23f = relwidthg ifl_f res23f.G
                if rw23f <= rprec && equaldf res23d.G res23f.G then
                    printfn "res= %A; rel width= %g" res23f rw23f
                    2,3,"f",res23f.Ubound.Value
                else
                    printfn "res= %A; rel width= %g" res23d rw23d
                    2,3,"d",res23d.Ubound.Value
            else if precision <= 5 then
                let res34d = exp.EvalUBG icr_34d
                let rw34d = relwidthg ifl_d res34d.G
                let res34f = exp.EvalUBG icr_34f
                let rw34f = relwidthg ifl_f res34f.G
                if rw34f <= rprec && equaldf res34d.G res34f.G then
                    printfn "res= %A; rel width= %g" res34f rw34f
                    3,4,"f",res34f.Ubound.Value
                else
                    printfn "res= %A; rel width= %g" res34d rw34d
                    3,4,"d",res34d.Ubound.Value
            else
                    let res46d = exp.EvalUBG icr_46d
                    let rw46d = relwidthg ifl_d res46d.G
                    let res46f = exp.EvalUBG icr_46f
                    let rw46f = relwidthg ifl_f res46f.G
                    if rw46f <= rprec && equaldf res46d.G res46f.G then
                        printfn "res= %A; rel width= %g" res46f rw46f
                        4,6,"f",res46f.Ubound.Value
                    else
                        printfn "res= %A; rel width= %g" res46d rw46d
                        4,6,"d",res46d.Ubound.Value

    let ComputeUB (exp:UboundExpression) precision =
        let icr_23f = ENV23f.IFrom
        let icr_23d = ENV23d.IFrom
        let icr_34f = ENV34f.IFrom
        let icr_34d = ENV34d.IFrom
        let icr_46f = ENV46f.IFrom
        let icr_46d = ENV46d.IFrom
        let ifl_f = SPFloat.IFloat
        let ifl_d = SPDFloat.IFloat
        let rprec = 10.0 ** (float -precision)
        if precision < 1 || precision > 12 then printfn "Compute: precision out of domain [1..12]";  0,0,"ERR",(icr_23f.from Double.NaN).ubound
        else
            if precision <= 2 then
                let res23d = exp.EvalUB icr_23d
                let rw23d = relwidth ENV23d.Env res23d.ubound
                let res23f = exp.EvalUB icr_23f
                let rw23f = relwidth ENV23f.Env res23f.ubound
                if rw23f <= rprec && equaldf res23d.G.Value res23f.G .Value then
                    printfn "res= %A; rel width= %g" res23f rw23f
                    2,3,"f",res23f.ubound
                else
                    printfn "res= %A; rel width= %g" res23d rw23d
                    2,3,"d",res23d.ubound
            else if precision <= 5 then
                let res34d = exp.EvalUB icr_34d
                let rw34d = relwidth ENV34d.Env res34d.ubound
                let res34f = exp.EvalUB icr_34f
                let rw34f = relwidth ENV34f.Env res34f.ubound
                if rw34f <= rprec && equaldf res34d.G.Value res34f.G.Value then
                    printfn "res= %A; rel width= %g" res34f rw34f
                    3,4,"f",res34f.ubound
                else
                    printfn "res= %A; rel width= %g" res34d rw34d
                    3,4,"d",res34d.ubound
            else
                let res46d = exp.EvalUB icr_46d
                let rw46d = relwidth ENV46d.Env res46d.ubound
                let res46f = exp.EvalUB icr_46f
                let rw46f = relwidth ENV46f.Env res46f.ubound
                if rw46f <= rprec && equaldf res46d.G.Value res46f.G.Value then
                    printfn "res= %A; rel width= %g" res46f rw46f
                    4,6,"f",res46f.ubound
                else
                    printfn "res= %A; rel width= %g" res46d rw46d
                    4,6,"d",res46d.ubound
