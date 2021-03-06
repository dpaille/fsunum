﻿(*

Copyright © Taylor & Francis Group, 2014.
Copyright © Daniel Paillé, 2018.

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the software.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES, OR OTHER LIABILITY, WHETHER IN AN ACTION OR CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

*)

(*
    Notes for the F# version:
    * unum numbers are not unbounded but stored in an uint64
    * the environement (env) is a separate type in order to have more than one environement setting at once
    * being 64 bits the env prototype values are complemented with values that ensure no overflow on a unum64.
      It then separates the values when they act as a mask from the ones that act as a maximum value.
    * "_nc" routines with no validity checking if unum(s) is(are) valid(s). It allows to make the test only once
      for methods that calls each other.
    * scratchpad is based on interface type ifl, which can be float, double-float, etc.
*)


namespace fsunum


module unum64 =
    open System
    open ifl

    type envsizes = {esizesize : int; fsizesize : int}
    type env<'F> = {
                    esizesize : int;
                    fsizesize : int;
                    esizemax : int;
                    espmax : int;
                    fsizemax : int;
                    fspmax : int;
                    utagsize : int;
                    maxubits : int;
                    ubitmask : uint64;
                    fsizemask : uint64;
                    esizemask : uint64;
                    efsizemask : uint64;
                    efsizevalmax : uint64;
                    utagmask : uint64;
                    ulpu : uint64;
                    smallsubnormalu : uint64;
                    smallnormalu : uint64;
                    signbigu : uint64;
                    posinfu : uint64;
                    maxrealu : uint64;
                    minrealu : uint64;
                    neginfu : uint64;
                    negbigu : uint64;
                    qNaNu : uint64;
                    sNaNu : uint64;
                    negopeninfu : uint64;
                    posopeninfu : uint64;
                    negopenzerou : uint64;
                    maxreal : float;
                    smallsubnormal : float;
                    smallnormal : float;
                    zerou : uint64;
                    oneu : uint64;
                    twou : uint64;
                    threeu : uint64;
                    sprecision : int;
                    ifl: IFloat<'F>;
                    floatinexactmask : uint64}

    // unum masks for a particular environment (exponent size, fraction size)
    // make an environment from the max width of exponent and fraction tag bit specifications
    // this environment contains the utility variables for manipulating unums
    let setenv_ esizesize fsizesize (ifl : IFloat<_>)=
        match esizesize, fsizesize with
        // f = 6 leads already to 64 bits mantissa which will not be representable in an uint64
        // e = 4 leads to 16 bits exponents which exceeds the float (double) capacity: 11 bits
        // the exponent size is limited to 10 which keeps max value in the float domain
        | e, f when e > 4 || f > 6 -> None
        | _ ->
            // e and f as aliases
            let e, f = esizesize, fsizesize
            // the maximum possible exponent size
            let esizemax = 1 <<< e
            // max exp size allowed by the scratchpad
            let espmax = min 10 esizemax
            // the maximum possible fraction size
            let fsizemax = 1 <<< f
            // the meta information (utag) size: 1 ubit + nb of exponent bits + nb of fraction bits
            let utagsize = 1 + f + e
            // a unum64 has to fit into 64 bits
            let fspmax = min (63 - espmax - utagsize) fsizemax 
            let sprecision = int ( floor(float (fspmax + 1) * log 2. / log 10.) ) // + 1
            // mask on Double that when ANDed with a number tells if it has more information than fspmax mantissa bits and is therefore inexact
            let floatinexactmask = (1UL <<< (fspmax + 1)) - 1UL
            // the maximum length of an unum
            let maxubits  = 1 + espmax + fspmax + utagsize
            // the mask for the ubit
            let ubitmask = 1UL <<< (utagsize - 1)
            // the mask for the fraction size meta data
            let fsizemask = (1UL <<< int f) - 1UL
            // the mask for the exponent size meta data
            // the ubitmask minus one fills the right part of the utag with ones
            // then subtracting the fsizemask gives only ones in the esize part
            let esizemask = ubitmask - 1UL - fsizemask
            // the mask for exponent and fraction meta fields (e and f)
            let efsizemask = esizemask ||| fsizemask
            // the max possible value in efsizemask
            //let espfsizemax = (uint64 (espmax - 1) <<< f) + fsizemask
            let efsizevalmax = (uint64 (espmax - 1) <<< f) + uint64 (fspmax - 1)
            // the mask for the whole utag
            let utagmask = ubitmask ||| efsizemask
            // the unit in the last place. One bit left from the ubit
            let ulpu = 1UL <<< utagsize
            // smallest subnormal: max exponent size and max fraction size, minimum exponent (0 minus bias) and ulpu 
            let smallsubnormalu = efsizevalmax + ulpu
            // small normal: ulpu with exponent to 1 minus bias
            let smallnormalu = efsizevalmax + ( 1UL <<< ( fsizemax + utagsize ) )
            // sign bit mask for maximum size unum: 1 in the (maxubits - 1) position
            let signbigu = 1UL <<< (maxubits - 1)
            // positive infinity: all bits to one except sign and ubit
            let posinfu = signbigu - 1UL - ubitmask
            // max (last) possible representable real: positive inf minus ulpu
            let maxrealu = posinfu - ulpu
            // minimum (max negative) possible representable real
            let minrealu = maxrealu + signbigu
            // negative infinity
            let neginfu = posinfu + signbigu
            // isn't that minrealu ???
            let negbigu = neginfu - ulpu
            // quiet NaN
            let qNaNu = posinfu + ubitmask
            // signaling NaN
            let sNaNu = neginfu + ubitmask
            let negopeninfu = if utagsize = 1 then 0b1101UL else 0b1111UL <<< (utagsize - 1)
            let posopeninfu = if utagsize = 1 then 0b0101UL else 0b0111UL <<< (utagsize - 1)
            let negopenzerou = 0b1001UL <<< (utagsize - 1)
            let maxreal = ( 2. ** (2. ** float (espmax - 1)) ) / ( 2. ** float (fspmax - 1) ) * ( ((2. ** float (fspmax)) - 1.)  )
            let smallsubnormal = 2. ** ( 2. - (2. ** float (espmax - 1)) - float fspmax )
            // smallnormalu as a float
            let smallnormal = 2. ** ( 2. - (2. ** float (espmax - 1)) )
            let zerou = 0UL
            let oneu = 1UL <<< (utagsize)
            let twou = 1UL <<< (utagsize + 1)
            let threeu = 0b11UL <<< (utagsize)
            Some {  esizesize = esizesize;
                    fsizesize = fsizesize;
                    esizemax = esizemax;
                    espmax = espmax;
                    fsizemax = fsizemax;
                    fspmax = fspmax;
                    utagsize = utagsize;
                    maxubits = maxubits;
                    ubitmask = ubitmask;
                    fsizemask = fsizemask;
                    esizemask = esizemask;
                    efsizemask = efsizemask;
                    efsizevalmax = efsizevalmax;
                    utagmask = utagmask;
                    ulpu = ulpu;
                    smallsubnormalu = smallsubnormalu;
                    smallnormalu = smallnormalu;
                    signbigu = signbigu;
                    posinfu = posinfu;
                    maxrealu = maxrealu;
                    minrealu = minrealu;
                    neginfu = neginfu;
                    negbigu = negbigu;
                    qNaNu = qNaNu;
                    sNaNu = sNaNu;
                    negopeninfu = negopeninfu;
                    posopeninfu = posopeninfu;
                    negopenzerou = negopenzerou;
                    maxreal = maxreal;
                    smallsubnormal = smallsubnormal;
                    smallnormal = smallnormal;
                    zerou = zerou;
                    oneu = oneu;
                    twou = twou;
                    threeu = threeu;
                    sprecision = sprecision;
                    ifl = ifl;
                    floatinexactmask = floatinexactmask}

    let setenv esizesize fsizesize ifl = match setenv_ esizesize fsizesize ifl with |Some(u) -> u | _ -> failwith "ERROR: wrong env"
    let setenvFromEnv env = setenv env.esizesize env.fsizesize env.ifl

    let gogreen = ConsoleColor.DarkCyan
    let cautionamber = ConsoleColor.DarkYellow
    let stopred = ConsoleColor.Red
    let red = ConsoleColor.Red
    let brightblue = ConsoleColor.Blue
    let sanegreen = ConsoleColor.DarkGreen
    let paleblue = ConsoleColor.Cyan
    let brightpurple = ConsoleColor.DarkMagenta
    let brightmagenta = ConsoleColor.Magenta
    let textamber = ConsoleColor.Yellow
    let chartreuse = ConsoleColor.Gray
    let gray = ConsoleColor.Gray
    let black = ConsoleColor.Black
    let white = ConsoleColor.White

    let toBinary i size =
        let lastbit k = k &&& 1UL
        let rec shiftRec j acc =
            match j with
            | 0UL -> acc
            | _ -> shiftRec (j >>> 1) (lastbit j :: acc)
        let l = shiftRec i []
        match l with
        | [] ->  if size <> 0 then (sprintf "%0*d" size 0) else ""
        | _ ->  let rl = List.rev l
                let mr = List.map (fun k -> if k = 1UL then "1" else "0") rl |> List.reduce (fun a b -> b + a)
                if size <> mr.Length then (sprintf "%0*d" (size - mr.Length) 0) + mr else mr

    // show the utag of an unum (as an uint64) in the Console with colors over 2 lines
    let utagview env u =
        let e = (u &&& env.esizemask) >>> int env.fsizesize
        let f = u &&& env.fsizemask
        let i = u &&& env.ubitmask
        Console.ForegroundColor <- brightmagenta 
        if i = 0UL then printf "0" else printf "1"
        Console.ForegroundColor <- gray
        printf "|"
        Console.ForegroundColor <- sanegreen
        let ess = int env.esizesize
        printf "%*s" ess (toBinary e ess)
        Console.ForegroundColor <- gray
        printf "|"
        Console.ForegroundColor <- gray
        let fss = (int env.fsizesize)
        printfn "%*s" fss (toBinary f fss)
        // second line
        Console.ForegroundColor <- gray
        if i = 0UL then printf "↓" else printf "…"
        Console.ForegroundColor <- gray
        printf "|"
        printf "%*i" ess (int e + 1)
        Console.ForegroundColor <- gray
        printf "|"
        printfn "%*i" fss (int f + 1)

    // Test if x is representable as a float. (Including exception values.)
    //let floatQ (x:float) = true

    // test if a value is a legitimate unum (for a given env)
    let inline unumQ env x = if x >= 0UL && x <= env.sNaNu then Some(x) else None
    let (|UnumQ|_|) env x = unumQ env x
    // values and bit masks for taking apart a unum bit string. Independent of the content of the utag.
    let ifUnumCompute env f = function | UnumQ env x -> f x |  x -> failwith <| sprintf "ERROR: not an unum: %d" x
    let if2UnumCompute env f x y = if Option.isSome <| unumQ env x then
                                        if Option.isSome <| unumQ env y then f x y
                                        else  failwith <| sprintf "ERROR: not an unum: %d" y
                                   else  failwith <| sprintf "ERROR: not an unum: %d" x
    let inline fsizeminus1_nc env x = x &&& env.fsizemask
    let fsizeminus1 env u = ifUnumCompute env (fun x -> fsizeminus1_nc env x) u
    let inline fsize_nc env x = 1UL + fsizeminus1_nc env x
    let fsize env u =  ifUnumCompute env (fun x -> fsize_nc env x) u
    let inline esizeminus1_nc env x = (x &&& env.esizemask) >>> env.fsizesize
    let esizeminus1 env u = ifUnumCompute env (fun x -> esizeminus1_nc env x) u
    let inline esize_nc env x =  1UL + esizeminus1_nc env x
    let esize env u =  ifUnumCompute env (fun x -> esize_nc env x) u
    let utag env esize fsize =
        if (esize >= 1 && esize <= env.espmax) &&
           (fsize >= 1 && fsize <= env.fspmax) then (fsize - 1) ||| ( (esize - 1) <<< env.fsizesize ) else failwith "ERROR: wrong arguments"
    let inline numbits_nc env x = 1 + int (esize_nc env x) + int (fsize_nc env x) + env.utagsize
    let numbits env u = ifUnumCompute env (fun x -> 1 + int (esize_nc env x) + int (fsize_nc env x) + env.utagsize) u
    let inline signmask_nc env x = 1UL <<< (numbits_nc env x - 1)
    let signmask env u = ifUnumCompute env (fun x -> signmask_nc env x) u
    let inline hiddenmask_nc env x = 1UL <<< (int (fsize_nc env x) + env.utagsize)
    let hiddenmask env u = ifUnumCompute env (fun x -> hiddenmask_nc env x) u
    let inline fracmask_nc env x = ( (1UL <<< (int (fsize_nc env x))) - 1UL ) <<< env.utagsize
    let fracmask env u = ifUnumCompute env (fun x -> fracmask_nc env x) u
    let inline expomask_nc env x = ( (1UL <<< (int (esize_nc env x))) - 1UL ) <<< (int (fsize_nc env x) + env.utagsize)
    let expomask env u = ifUnumCompute env (fun x -> expomask_nc env x) u
    let inline floatmask_nc env x = signmask_nc env x + expomask_nc env x + fracmask_nc env x
    let floatmask env u = ifUnumCompute env (fun x -> floatmask_nc env x) u
    // values and bit masks that dependent on what is stored in the utag.
    let inline bias_nc env x = (1UL <<< int (esizeminus1_nc env x)) - 1UL
    let bias env u = ifUnumCompute env (fun x -> bias_nc env x) u
    let inline Boole expr = if expr then 1 else 0
    let inline BooleU expr = if expr then 1UL else 0UL
    let inline sign_nc env x = Boole (x &&& signmask_nc env x > 0UL)
    let sign env u = ifUnumCompute env (fun x -> sign_nc env x) u
    let inline expo_nc env x = (x &&& expomask_nc env x) >>> (env.utagsize + int (fsize_nc env x))
    let expo env u = ifUnumCompute env (fun x -> expo_nc env x) u
    let inline hidden_nc env x = Boole (expo_nc env x > 0UL)
    let hidden env u = ifUnumCompute env (fun x -> hidden_nc env x) u
    let inline frac_nc env x = (x &&& fracmask_nc env x) >>> env.utagsize
    let frac env u = ifUnumCompute env (fun x -> frac_nc env x) u
    let inline inexQ_nc env x = x &&& env.ubitmask > 0UL
    let inexQ env u = ifUnumCompute env (fun x -> inexQ_nc env x) u
    let inline exQ_nc env x = x &&& env.ubitmask = 0UL
    let exQ env u = ifUnumCompute env (fun x -> exQ_nc env x) u
    let inline exact_nc env x = if inexQ_nc env x then x ^^^ env.ubitmask else x
    let exact env u = ifUnumCompute env (fun x -> exact_nc env x) u

    // display the six fields of a unum bit string, color-coded and spaced.
    let colorcode env u =
        ifUnumCompute env (fun x -> 
            Console.ForegroundColor <- red 
            if sign_nc env x = 0 then printf "0" else printf "1"
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- brightblue
            let esx = int <| esize_nc env x
            printf "%*s" esx (toBinary (expo_nc env x) esx)
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- gray
            let fsx = int <| fsize_nc env x
            printf "%*s" fsx (toBinary <| frac_nc env x <| fsx)
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- brightmagenta
            if inexQ_nc env x then printf "1" else printf "0"
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- sanegreen
            printf "%*s" env.esizesize (toBinary <| esizeminus1_nc env x <| env.esizesize)
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- gray
            printfn "%*s" env.fsizesize (toBinary <| fsizeminus1_nc env x <| env.fsizesize)
            ()
        ) u

    // numerical value meant by exponent bits; helper function for u2f
    let inline expovalue_nc env x = int (expo_nc env x) - int (bias_nc env x) + 1 - hidden_nc env x
    let expovalue env u = ifUnumCompute env (fun x -> expovalue_nc env x) u

    // convert an exact unum to its float value.
    let inline exactUnumQ env x = if exQ_nc env x && x >= 0UL && x <= env.sNaNu then Some(x) else None
    let (|ExactUnumQ|_|) env x = exactUnumQ env x
    let ifExactUnumCompute env f = function | ExactUnumQ env x -> f x |  x -> failwith <| sprintf "ERROR: not an exact unum: %d" x
    let if2ExactUnumCompute env f x y = match (exactUnumQ env x), (exactUnumQ env y) with
                                        | Some(x_), Some(y_) -> f x_ y_ 
                                        | None, Some(y_) -> failwith <| sprintf "ERROR: not an exact unum: %d" x
                                        | Some(x_), None -> failwith <| sprintf "ERROR: not an exact unum: %d" y
                                        | _ -> failwith <| sprintf "ERROR: not exact unums: %d, %d" x y
    let u2f_nc env x  =
        let ifl = env.ifl 
        if x = env.posinfu then ifl.PosInf
        elif x = env.neginfu then ifl.NegInf
        else
            let signf = float (sign_nc env x)
            let hiddenf = float (hidden_nc env x)
            let fracf = float (frac_nc env x)
            let fsizei = int (fsize_nc env x)
            let fsizef = float (fsizei)
            let expovaluef = float ((x &&& expomask_nc env x) >>> (env.utagsize + fsizei))
                             - float (bias_nc env x) + 1. - hiddenf
            let res = (-1. ** signf) * ( 2. ** expovaluef ) * ( hiddenf + fracf / (2. ** fsizef) )
            ifl.from res
    let u2f env u = ifExactUnumCompute env ( fun x -> u2f_nc env x ) u

    // Biggest unum possible with identical utag contents.
    let bigu_nc env u = expomask_nc env u + fracmask_nc env u + (env.efsizemask &&& u)
                        // decrease by ulpu if u has the maximum possible value in efsizemask
                        - env.ulpu * BooleU (u &&& env.efsizevalmax = env.efsizevalmax) 
    let bigu env u_ = ifUnumCompute env  (fun u -> bigu_nc env u) u_
    // Biggest numerical value representable with identical utag contents.
    let big_nc env x = u2f_nc env <| bigu_nc env x
    let big env u = ifUnumCompute env (fun x -> big_nc env x) u

    let unumDecimalView env u =
        if u = env.qNaNu || u = env.sNaNu then
            "NaN"
        elif u = env.posinfu then
            "+Inf"
        elif u = env.neginfu then
            "-Inf"
        else
            let esx = int <| esize_nc env u
            let ex = expo_nc env u
            let fsx = int <| fsize_nc env u
            let fx = frac_nc env u
            let s = sign_nc env u
            let sstr = if s = 0 then "" else "-"
            let ev = expovalue_nc env u
            let dbi0 = 1I <<< fsx
            let nbi =
                if ex > 0UL then
                    bigint fx + dbi0
                else
                    bigint fx
            let zi = fsx - ev
            let mutable r = 0I
            let nbi_, dbi_ =
                if zi < 0 then
                   nbi * (1I <<< -zi), 1I
                elif zi = 0 then
                   nbi, 1I
                else
                   nbi, dbi0 >>> ev
            let e = bigint.DivRem(nbi_, dbi_, &r)
            if dbi_ = 1I || r = 0I then
                sstr + e.ToString()
            else
                let f = (r * 10I **  zi) / dbi_
                let fstr = f.ToString()
                let padzero = String.init (zi - fstr.Length) (fun i -> "0")
                sstr + e.ToString() + "." + padzero + fstr.TrimEnd('0')

    let unumview env u =
        ifUnumCompute env (fun x -> 
            Console.ForegroundColor <- red 
            let s = sign_nc env x
            if s = 0 then printf "0" else printf "1"
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- brightblue
            let esx = int <| esize_nc env x
            let ex = expo_nc env x
            printf "%*s" esx (toBinary ex esx)
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- gray
            let fsx = int <| fsize_nc env x
            let fx = frac_nc env x
            printf "%*s" fsx (toBinary fx fsx)
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- brightmagenta
            let inex = inexQ_nc env x
            if inex then printf "1" else printf "0"
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- sanegreen
            printf "%*s" env.esizesize (toBinary (esizeminus1_nc env x) env.esizesize)
            Console.ForegroundColor <- gray
            printf "|"
            Console.ForegroundColor <- gray
            let fs1 = fsizeminus1_nc env x
            printfn "%*s" env.fsizesize (toBinary fs1 env.fsizesize)
            if u = env.qNaNu || u = env.sNaNu then
                printfn "NaN"
            elif u = env.posinfu then
                printfn "+Inf"
            elif u = env.neginfu then
                printfn "-Inf"
            else
                Console.ForegroundColor <- red 
                if s = 0 then printf "+ " else printf "- "
                Console.ForegroundColor <- gray
                // exponent
                Console.ForegroundColor <- brightblue
                let ev = expovalue_nc env x
                printfn "2^%i x" ev
                // fraction
                Console.ForegroundColor <- gray
                let fpos = 3 + esx
                let padf = String.init fpos (fun i -> " ")
                let h = if ex = 0UL then "(0+" else "(1+"
                printfn "%s%s %i/%i)" padf h fx ( 1UL <<< fsx )
                let utagpos = fpos + 1 + fsx
                let pad = String.init utagpos (fun i -> " ")
                Console.ForegroundColor <- gray
                printf "%s" pad
                if not inex then printf "↓" else printf "…"
                Console.ForegroundColor <- gray
                printf "|"
                printf "%*i" (int env.esizesize) esx
                Console.ForegroundColor <- gray
                printf "|"
                printfn "%*i" (int env.fsizesize) fsx 
                let f = u2f_nc env x
                if not inex then
                    printfn "= %s" (unumDecimalView env x)
                else
                    let bu = bigu_nc env x
                    if exact_nc env x = bu then
                        let fbu = u2f_nc env bu
                        printfn "= (%s, +Inf)" (unumDecimalView env bu)
                    elif exact_nc env x = bu + signmask_nc env x then
                        let fbu = u2f_nc env bu
                        printfn "= (-Inf, -%s)" (unumDecimalView env bu)
                    else
                    let up = x + env.ulpu
                    let fup = u2f_nc env up
                    if s = 0 then
                        printfn "= (%s, %s)"  (unumDecimalView env x) (unumDecimalView env up)
                    else
                        printfn "= (%s, %s)" (unumDecimalView env up)  (unumDecimalView env x)
            ()
        ) u                    


    // Some synonyms.
    let Open, Closed = true, false
    
    let unum2g_nc env u =
        let ifl = env.ifl
        if u = env.qNaNu || u = env.sNaNu then ((ifl.NaN, ifl.NaN), (Open, Open))
        else
        let x = u2f_nc env (exact_nc env u)
        if exQ_nc env u then ((x, x), (Closed, Closed))
        else
            let bu = bigu_nc env u
            let buf = u2f_nc env bu
            let bupubm = bu + env.ubitmask
            if u = bupubm then (buf, ifl.PosInf), (Open, Open)
            elif u = (signmask_nc env u) + bupubm then (ifl.NegInf, ifl.negate buf), (Open, Open)
            else
                let xpulp = u2f_nc env (exact_nc env u + env.ulpu)
                if sign_nc env u = 1 then (xpulp, x), (Open, Open)
                else (x, xpulp), (Open, Open)

    let unum2g env u_ =
        ifUnumCompute env
            ( fun u -> 
                unum2g_nc env u
            ) u_

    // Trivial expression of a floatable value in the form of a general interval.
    let f2g (ifl : IFloat<_>) x = if ifl.IsNaN x then (ifl.NaN, ifl.NaN),(Open, Open) else (x,x),(Closed, Closed)

    // helper functions for general interval
    let leftFloat (g : ('F*'F) * (bool*bool)) = fst <| fst g
    let leftInterval (g : ('F*'F) * (bool*bool)) = fst <| snd g
    let rightFloat (g : ('F*'F) * (bool*bool)) = snd <| fst g
    let rightInterval (g : ('F*'F) * (bool*bool)) = snd <| snd g

    type ubound = | Unum of uint64 | Bounds of uint64 * uint64

    let uboundQ env = function
        | Unum(u) -> unumQ env u |> Option.isSome
        | Bounds(xL,xR) ->
            if xL = env.qNaNu || xL = env.sNaNu || xR = env.qNaNu || xR = env.sNaNu then true
            else
                let gL, gR = (unum2g_nc env xL), (unum2g_nc env xR)
                if (leftFloat gL < rightFloat gR) || ((leftFloat gL = rightFloat gR) && (exQ env xL && exQ env xR))  then true
                else false

    let ifUboundCompute env f xb  = if uboundQ env xb then f xb  else failwith <| sprintf "ERROR: not an ubound: %A" xb

    let if2UboundCompute env f xb yb = if uboundQ env xb then
                                            if  uboundQ env yb then f xb yb
                                            else  failwith <| sprintf "ERROR: not an ubound: %A" yb
                                       else  failwith <| sprintf "ERROR: not an ubound: %A" xb
    let if3UboundCompute env f xb yb zb = if uboundQ env xb then
                                            if  uboundQ env yb then
                                                if  uboundQ env yb then f xb yb zb
                                                else  failwith <| sprintf "ERROR: not an ubound: %A" zb
                                            else  failwith <| sprintf "ERROR: not an ubound: %A" yb
                                          else  failwith <| sprintf "ERROR: not an ubound: %A" xb
    let ifUboundListCompute env f l =
        let notuboundQenv = not << uboundQ env 
        if not <| List.exists (notuboundQenv) l then f l else failwith "ERROR: not an ubound in list"

    let fstBound ub = match ub with | Unum(v) -> v | Bounds(v,_) -> v

    let sndBound ub = match ub with | Unum(v) -> v | Bounds(_,v) -> v

    let uboundview env ub =
        ifUboundCompute env ( fun x -> 
            match x with
            | Unum(u) -> unumview env u
            | Bounds(u,v) ->
                if exQ_nc env u then
                    printfn "["
                    unumview env u
                else
                    printfn "("
                    let su = sign_nc env u
                    if su <> 0 then
                       let ue = (exact_nc env u) + env.ulpu
                       unumview env ue
                    else
                       unumview env (exact_nc env u)
                printfn ", "
                if exQ_nc env v then
                    unumview env v
                    printfn "]"
                else
                    let sv = sign_nc env v
                    if sv <> 0 then
                        unumview env (exact_nc env v)
                    else
                        let ve = (exact_nc env v) + env.ulpu
                        unumview env ve                      
                    printfn ")"
        ) ub


    let gQ (ifl : IFloat<_>) (g : ('F*'F) * (bool*bool)) =
        let leftfloat = leftFloat g
        let rightfloat = rightFloat g
        if ifl.IsNaN leftfloat || ifl.IsNaN rightfloat then true
        elif leftfloat = rightfloat && not (leftInterval g) && not (rightInterval g) || leftfloat < rightfloat then true
        else false

    let ifGCompute ifl f g = if gQ ifl g then f g else failwith <| sprintf "ERROR: not a general interval: %A" g

    let if2GCompute ifl f xg yg = if gQ ifl xg then
                                    if  gQ ifl yg then f xg yg
                                    else  failwith <| sprintf "ERROR: not a general interval: %A" yg
                                  else  failwith <| sprintf "ERROR: not a general interval: %A" xg
    
    let ubound2g_nc env = function
        | Unum(u) -> unum2g_nc env u
        | Bounds(xL,xR) ->
            if xL = env.qNaNu || xL = env.sNaNu  || xR = env.qNaNu || xR = env.sNaNu then
                (env.ifl.NaN,env.ifl.NaN),(Open,Open)
            else
                let gL, gR = unum2g_nc env xL, unum2g_nc env xR
                (leftFloat gL, rightFloat gR), (leftInterval gL, rightInterval gR)

    let ubound2g env = function
        | Unum(u) -> unum2g env u
        | Bounds(xL,xR) ->
            if xL = env.qNaNu || xL = env.sNaNu  || xR = env.qNaNu || xR = env.sNaNu then
                (env.ifl.NaN, env.ifl.NaN), (Open, Open)
            else
                let gL, gR = unum2g env xL, unum2g env xR
                (leftFloat gL, rightFloat gR), (leftInterval gL, rightInterval gR)
    
    let rec fWhile p f x = if p x then fWhile p f (f x) else x
    
    let log2 x = Math.Log (x, 2.)

    // find the scale factor
    let scale (ifl : IFloat<_>) x = if x = ifl.Zero then 0 else int ( floor ( ifl.float ( ifl.log2 (ifl.abs x) ) ) )

    // find best number of scale bits
    let ne (ifl : IFloat<_>) x =
               if x = ifl.Zero && scale ifl x = ifl.One then 1
               else
                    let n = ( Log2 ( 1. + Abs (From (float (scale ifl x)) - 1.) ) ).Eval ifl
                    1 + int ( ceil ( ifl.float n ) )

    // same than ne x but using scale x 
    let ne_sc (ifl : IFloat<_>) x scalex = if x = ifl.Zero && scalex = 1 then 1
                                           else
                                                let n = ( Log2 ( 1. + Abs (From (float scalex) - 1.) ) ).Eval ifl
                                                1 + int ( ceil ( ifl.float n ) )

    let IsInteger (ifl : IFloat<_>) z_ = ifl.floor z_ = z_

    // convert a ifl to a unum
    // Conversion of a floatable real to a unum. Same as the "^" annotation.
    // Most of the complexity stems from seeking the shortest possible bit string.
    let IsPosInf (ifl : IFloat<_>) x = ifl.IsInf x && x > ifl.Zero
    let IsNegInf (ifl : IFloat<_>) x = ifl.IsInf x && x < ifl.Zero
    let x2u env x =
        let ifl = env.ifl
        // Exceptional nonnumeric values:
        if ifl.IsNaN x then env.qNaNu
        elif IsPosInf ifl x then env.posinfu
        elif IsNegInf ifl x then env.neginfu
        else
        let absx = ifl.abs x
        // Magnitudes too large to represent:
        if absx > ifl.from env.maxreal then env.maxrealu + env.ubitmask + (if x < ifl.Zero then env.signbigu else 0UL)
        // Zero is a special case. The smallest unum for it is just 0:
        elif x = ifl.Zero then 0UL
        // Magnitudes too small to represent become "inexact zero" with
        // the maximum exponent and fraction field sizes:
        elif absx < ifl.from env.smallsubnormal then env.utagmask + (if x < ifl.Zero then env.signbigu else 0UL)
        // For subnormal numbers, divide by the ULP value to get the
        // fractional part. The while loop strips off the trailing bits.
        elif absx < ifl.from env.smallnormal then
            let y0 = ( Val absx  / env.smallsubnormal ).Eval ifl
            let y1 = (if x < ifl.Zero then env.signbigu else 0UL)
                     + env.efsizevalmax + (if y0 <> ifl.floor y0 then env.ubitmask  else 0UL)
                     + ( (uint64 (ifl.float (ifl.floor y0))) <<< env.utagsize )
            fWhile ( fun z -> (3UL <<< (env.utagsize - 1)) &&& z = 0UL )
                   ( fun z -> let efz = env.efsizemask &&& z
                              (z - efz) / 2UL + efz - 1UL )
                   y1
        // All remaining cases are in the normalized range.
        else
            let n0 = 0
            let scalex = scale ifl x
            let y0 = ( Val absx / Npwr( From 2., scalex) ).Eval ifl
            let n, y = fWhile (fun (n_, y_) -> ifl.floor y_ <> y_ && n_ < env.fspmax)
                              (fun (n_, y_) -> (n_ + 1, ifl.timesrfloat (y_, 2.)))
                              (n0, y0)
            let nex = ne_sc ifl x scalex
            if y = ifl.floor y then
                // then the value is representable exactly. Fill in the fields from right to left:
                // Size of fraction field, fits in the rightmost fsizesize bits...
                let yint = int64 <| ifl.float y
                let significands = (uint64 ( yint - pown 2L (scale ifl y) ) <<< env.utagsize)
                let y1 = uint64 n - BooleU (n > 0)
                        // Size of exponent field minus 1 fits in the esizesize bits...
                        + (uint64 (nex - 1) <<< env.fsizesize)
                        // Significant bits after hidden bit fits left of the unum tag bits...
                        + if n = 0 then 0UL else (uint64 ( yint - pown 2L (scale ifl y) ) <<< env.utagsize)
                        // Value of exponent bits, adjusted for bias...
                        +  ( (uint64 ( scalex + pown 2 (nex - 1) ) - 1UL ) <<< (env.utagsize + n + Boole (n = 0)) )
                        // If negative, add the sign bit
                        + if x < ifl.Zero then 1UL <<< (env.utagsize + n + Boole (n = 0) + nex ) else 0UL
                // if a number is more concise as a subnormal, make it one
                let log2absx = (Log2 ( Val absx )).Eval ifl
                if log2absx < ifl.One then
                    let z = ( Log2 (1. - Val log2absx) ).Eval ifl
                    if IsInteger ifl z && z >= ifl.Zero then
                        let zu = uint64 (ifl.float z)
                        (zu <<< env.fsizesize) + env.ulpu + ( BooleU (x < ifl.Zero) * signmask env (zu <<< env.fsizesize) )
                    else y1
                else y1
            else
                // inexact. Use all available fraction bits
                let z0 = ( Npwr(From 2., scalex - env.fspmax) ).Eval ifl
                let z = ( Ceil( Val absx  / Val z0 ) * Val z0 ).Eval ifl
                let scalez= scale ifl z
                let nez = ne_sc ifl z scalez
                let n = max nex nez
                // All bits on for the fraction size, since we're using the maximum
                // The maximum is fspmax bits for the fraction minus one.
                let y1 = uint64 env.fspmax - 1UL
                         // Store the exponent size minus 1 in the exponent size field
                         + ((uint64 (n - 1)) <<< env.fsizesize)
                         // Back off by one ULP and make it inexact
                         + env.ubitmask - env.ulpu
                         // Fraction bits are the ones to the left of the
                         // binary point after removing hidden bit and scaling
                         + (uint64 ( floor ( ifl. float ( ( (Val z / Npwr (From 2., scalez)  - 1.) * Npwr( From 2., env.fspmax)).Eval ifl ) ) ) <<< env.utagsize)
                         // Exponent value goes in the exponent field
                         + (uint64 ( scalez + pown 2 (n - 1) - 1 ) <<< (env.utagsize + env.fspmax))
                if x < ifl.Zero then y1 + signmask env y1 else y1
 
    let printAtPrecisionIF env g prec =
        let ifl = env.ifl
        let s = ifl.sprint g
        let i = max (s.IndexOf('e')) (s.IndexOf('E'))
        let len = s.Length
        let lastDigit = if i <> -1 then i - 1 else len - 1
        let firstSignificantDigit = fWhile ( fun k -> s.[k] = '0' ||  s.[k] = '.' ) (fun k -> k + 1) 0
        let dotDigit = s.IndexOf('.')
        let dotPresent = dotDigit <> -1
        let numberOfSignificantDigits =
            if dotPresent then
                if firstSignificantDigit > dotDigit then
                    lastDigit - firstSignificantDigit + 1
                else
                    lastDigit
            else
                lastDigit + 1
        let s1 =
            if numberOfSignificantDigits <= prec then
                s
            else
                let exponent = if i = -1 then "" else s.Substring(i)
                let shiftRight =
                    if not dotPresent then
                        0
                    elif firstSignificantDigit > dotDigit then
                        firstSignificantDigit
                    else
                        1
                let s2 = s.Substring( 0, prec + shiftRight)
                if dotPresent then
                    sprintf "%s%s" ( s2.TrimEnd('0').TrimEnd('.') ) exponent
                else
                    sprintf "%sE%d" ((s2.Substring(0,1) + "." + s2.Substring(1).TrimEnd('0')).TrimEnd('.')) (lastDigit)
        s1

    let incrementAtPrecision env g prec =
        let ifl = env.ifl
        let fl = ifl.floor g
        // intpartlen = floor( log10 fl ) + 1. numbers of digits above zero
        let integerPartLength = if fl <= ifl.Zero then 0 else int (ifl.float( ifl.plus (ifl.floor( ifl.log10 fl ), ifl.One) ) )
        let fsb, _ =
            fWhile (fun (k, x) -> ifl.floor x = ifl.Zero )
                ( fun (k, x) ->
                    let x0 = ifl.times (x, ifl.Ten)
                    k + 1, x0
                ) (0, g)
        let pE = if integerPartLength <> 0 then prec - integerPartLength else  prec + fsb - 1
        let precisionExponent = ifl.create( float pE )
        // clean under 10^-z and add 1 at 10^-z
        let tensPowersToPrecision = ifl.Pow( ifl.Ten, precisionExponent )
        let tenthsDownToPrecision = ifl.Pow( ifl.Ten, ifl.negate precisionExponent )
        // ( (floor(g * 10. ** z)) * 10.** -z ) + 10. ** -z
        let valueShiftedAndCleaned = ifl.floor ( ifl.times (g, tensPowersToPrecision) )
        let valueCleaned = ifl.times (valueShiftedAndCleaned, tenthsDownToPrecision)
        let valueCleanedIncrementedInTheLastPlace = ifl.plus ( valueCleaned, tenthsDownToPrecision )
        valueCleanedIncrementedInTheLastPlace

    let rec autoNLow env g prec =
        let ifl = env.ifl 
        if g = ifl.Zero then "0"
        elif ifl.IsNaN g || ifl.IsInf g then ifl.sprint g
        elif g < ifl.Zero then "-" + (autoNLow env (ifl.negate g) prec)
        else
            printAtPrecisionIF env g prec

    let rec autoNHigh env g prec =
        let ifl = env.ifl 
        if g = ifl.Zero then "0"
        elif ifl.IsNaN g || ifl.IsInf g then ifl.sprint g
        elif g < ifl.Zero then "-" + (autoNHigh env (ifl.negate g) prec)
        else
            let g1 = incrementAtPrecision env g (prec+1)
            printAtPrecisionIF env g1 (prec+1)

    let viewAtPrec env g prec =
        let ifl = env.ifl
        let ((L,R),(LQ,RQ)) = g
        if ifl.IsNaN L || ifl.IsNaN R then "NaN"
        elif L = R && not LQ && not RQ then autoNLow env L prec
        else
            if L < R then
                let autoNL, autoNR =
                    if L < ifl.Zero && R <= ifl.Zero then
                        let autoNR_ = autoNLow env R  prec
                        let autoNL_ = autoNHigh env L prec
                        //let autoNL_ = autoNLow env L prec
                        //let autoNR_ = autoNHigh env R  prec
                        autoNL_, autoNR_
                    elif L < ifl.Zero && R > ifl.Zero then
                        let autoNL_ = autoNHigh env L prec
                        let autoNR_ = autoNLow env R  prec
                        autoNL_, autoNR_
                    else
                        let autoNL_ = autoNLow env L  prec
                        let autoNR_ = autoNHigh env R prec
                        autoNL_, autoNR_
                (if LQ then "(" else "[") +
                autoNL +
                ", " +
                autoNR +
                (if RQ then ")" else "]")
            else "NaN"

    let view env g = viewAtPrec env g env.sprecision

    // view number as exact decimals
    let viewAsExactUnums env L R =
        let LQ = inexQ_nc env L
        let RQ = inexQ_nc env R
        if L = env.qNaNu || L = env.sNaNu || R = env.qNaNu || R = env.sNaNu then "NaN"
        elif L = R && not LQ && not RQ then unumDecimalView env L
        else
            let autoNL =
                if not LQ then
                    unumDecimalView env L
                else
                    let sL = sign_nc env L
                    if sL <> 0 then
                        let LpUlp = (exact_nc env L) + env.ulpu
                        unumDecimalView env LpUlp
                    else
                        //unumDecimalView env (exact_nc env L)
                        unumDecimalView env L
            let autoNR =
                if not RQ then
                    unumDecimalView env R
                else
                    let sR = sign_nc env R
                    if sR <> 0 then
                        //unumDecimalView env (exact_nc env R)
                        unumDecimalView env R
                    else
                        let RpUlp = (exact_nc env R) + env.ulpu
                        unumDecimalView env RpUlp
            (if LQ then "(" else "[") +
            autoNL +
            ", " +
            autoNR +
            (if RQ then ")" else "]")

    let viewUB env ub = let u, v = match ub with | Unum u -> u, u | Bounds (u, v) -> u, v in viewAsExactUnums env u v
    let viewU env u = viewAsExactUnums env u u


    let plusg (ifl : IFloat<_>) x y =
        let ((xlo, xhi), (xlob, xhib)) = x
        let ((ylo, yhi), (ylob, yhib)) = y
        if  ifl.IsNaN xlo || ifl.IsNaN xhi || ifl.IsNaN ylo || ifl.IsNaN yhi  then (ifl.NaN, ifl.NaN), (Open, Open)
        else
            // compute the lower part of the sum ("lo" in the variable)
            let sumleft, openleft = if xlo = ifl.NegInf && not xlob then // [-inf + y?
                                        if ylo = ifl.PosInf && not ylob then ifl.NaN, Open // [-inf + [+inf = NaN
                                        else ifl.NegInf, Closed // else [-inf + y? = [-inf 
                                    elif ylo = ifl.NegInf && not ylob then // else x? + [-inf
                                        if xlo = ifl.PosInf && not xlob then ifl.NaN, Open // [+inf + [-inf = NaN
                                        else ifl.NegInf, Closed // else x? + [-inf = [-inf
                                    elif (xlo = ifl.PosInf && not xlob) || (ylo = ifl.PosInf && not ylob) then ifl.PosInf, Closed // else [+inf + y? = x? + [+inf = [+inf
                                    //elif xlo = NegInf || ylo = NegInf then NegInf, Open // else (-inf + y? = x? + (-inf = (-inf
                                    elif xlo = ifl.NegInf then
                                        if ylo = ifl.PosInf && not ylob then ifl.PosInf, Closed else ifl.NegInf, Open
                                    elif ylo = ifl.NegInf then
                                        if xlo = ifl.PosInf && not xlob then ifl.PosInf, Closed else ifl.NegInf, Open
                                    //ylo = NegInf then NegInf, Open // else (-inf + y? = x? + (-inf = (-inf
                                    else
                                        ifl.plus(xlo, ylo), xlob || ylob
            // compute the higher part of the sum ("hi" in the variable)
            let sumright, openright = if xhi = ifl.NegInf && not xhib then // -inf] + y? 
                                          if yhi = ifl.PosInf && not yhib then ifl.NaN, Open // -inf] + +inf] = NaN
                                          else ifl.NegInf, Closed // else -inf] + y? = -inf]
                                      elif yhi = ifl.NegInf && not yhib then // else x? + -inf]
                                          if xhi = ifl.PosInf && not xhib then ifl.NaN, Open // +inf] + -inf] = NaN
                                          else ifl.NegInf, Closed // else x? + -inf] = -inf]
                                      elif (xhi = ifl.PosInf && not xhib) || (yhi = ifl.PosInf && not yhib) then ifl.PosInf, Closed // else +inf] + y? = x? + +inf] = +inf]
                                      //elif xhi = NegInf || yhi = NegInf then NegInf, Open // else -inf) + y? = x? + -inf) = -inf)
                                      elif xhi = ifl.PosInf  then
                                          if yhi = ifl.NegInf && not yhib then ifl.NegInf,Closed else ifl.PosInf, Open
                                      
                                      elif yhi = ifl.PosInf then 
                                          if xhi = ifl.NegInf && not xhib then ifl.NegInf,Closed else ifl.PosInf, Open
                                      else
                                            ifl.plus(xhi, yhi), xhib || yhib
            (sumleft,sumright),(openleft,openright)

    // Test if interval g is strictly less than interval h.
    let ltgQ (ifl : IFloat<_>) g h =
            let glo, ghi = leftFloat g, rightFloat g
            let hlo, hhi = leftFloat h, rightFloat h
            let ghib, hlob = rightInterval g, leftInterval h
            //if Double.IsNaN glo || Double.IsNaN ghi || Double.IsNaN hlo || Double.IsNaN hhi then false
            if ifl.IsNaN glo || ifl.IsNaN ghi || ifl.IsNaN hlo || ifl.IsNaN hhi then false
            else ghi < hlo || (ghi = hlo && ( ghib || hlob ))

    // Test if ubound or unum u is strictly less than ubound or unum v.
    let ltuQ env ub vb = ltgQ env.ifl (ubound2g_nc env ub)(ubound2g_nc env vb)

    // Test if interval g is strictly greater than interval h.
    let gtgQ (ifl : IFloat<_>) g h =
            let glo, ghi = leftFloat g, rightFloat g
            let hlo, hhi = leftFloat h, rightFloat h
            let glob, hhib = leftInterval g, rightInterval h
            if ifl.IsNaN glo || ifl.IsNaN ghi || ifl.IsNaN hlo  || ifl.IsNaN hhi then false
            else glo > hhi || (glo = hhi && (glob || hhib))

    // Test if unum or ubound ub is strictly greater than unum or ubound  vb.
    let gtuQ env ub vb = gtgQ env.ifl (ubound2g_nc env ub)(ubound2g_nc env vb)

    // Test if interval g is nowhere equal to interval h.
    let neqgQ (ifl : IFloat<_>) g h =
        //if Double.IsNaN <| leftFloat g || Double.IsNaN <| rightFloat g || Double.IsNaN <| leftFloat h || Double.IsNaN <| rightFloat h then false
        if ifl.IsNaN <| leftFloat g || ifl.IsNaN <| rightFloat g || ifl.IsNaN <| leftFloat h || ifl.IsNaN <| rightFloat h then false
        else ltgQ ifl g h ||  gtgQ ifl g h

    // Test if ubound or unum u is nowhere equal to ubound or unum v.
    let nequQ env ub_ vb_ = if2UboundCompute env ( fun ub vb -> neqgQ env.ifl (ubound2g_nc env ub) (ubound2g_nc env vb) ) ub_ vb_

    // Test if interval g is not nowhere equal to interval h
    let nneqgQ (ifl : IFloat<_>) g h =
            let glo, ghi = leftFloat g, rightFloat g
            let hlo, hhi = leftFloat h, rightFloat h
            let glob, hhib = leftInterval g, rightInterval h
            //if Double.IsNaN glo || Double.IsNaN ghi || Double.IsNaN hlo  || Double.IsNaN hhi then false
            if ifl.IsNaN glo || ifl.IsNaN ghi || ifl.IsNaN hlo  || ifl.IsNaN hhi then false
            else not (ltgQ ifl g h || gtgQ ifl g h)

    // Test if ubound ub is not nowhere equal to ubound v
    let nnequQ_nc env ub vb = nneqgQ env.ifl (ubound2g_nc env ub) (ubound2g_nc env vb)
    let nnequQ env ub vb = if2UboundCompute env (fun xb yb -> nneqgQ env.ifl (ubound2g_nc env xb) (ubound2g_nc env yb)) ub vb

    // Test if interval g is identical to interval h
    let samegQ ifl g h = if2GCompute ifl (=) g h

    // Test if ubound or unum u value is identical to ubound or unum v value.
    let sameuQ env ub vb = if2UboundCompute env (fun xb yb -> ubound2g_nc env xb = ubound2g_nc env yb) ub vb

    let (===) env u v = sameuQ env u v

    // Find the intersection of two general intervals in the g - layer.
    let intersectg_nc (ifl : IFloat<_>) xg yg =
        let (glo, ghi),(glob, ghib) = xg
        let (hlo, hhi),(hlob, hhib)= yg
        if ifl.IsNaN glo || ifl.IsNaN ghi || ifl.IsNaN hlo || ifl.IsNaN hhi then (ifl.NaN,ifl.NaN),(Open,Open)
        elif glo < hlo || (glo = hlo && hlob) then
            // left end of g is left end of h. Three sub-cases to test.
            if ghi < hlo || (ghi = hlo && (ghib || hlob)) then (ifl.NaN,ifl.NaN),(Open,Open) // g is completly left of h
            elif ghi < hhi || (ghi = hhi && (ghib || not hhib)) then (hlo, ghi), (hlob, ghib) // right part of g overlaps left part of h.
            else (hlo, hhi), (hlob, hhib) // h is entirely inside g.
        elif glo < hhi || (glo = hhi && (not glob && not hhib)) then
            // left end of g is inside h. Two sub-cases to test.
            if ghi < hhi || (ghi = hhi && (ghib || not hhib)) then (glo, ghi), (glob, ghib) // g is entirely inside h.
            // left end of g overlaps right end of h.
            else (glo, hhi), (glob, hhib)
        else (ifl.NaN,ifl.NaN),(Open,Open) // g is entirely to the right of h

    let intersectg ifl g h = if2GCompute ifl (intersectg_nc ifl) g h

    // apply low pass filter from first argument to second
    let lowpassg ifl g h =
        if2GCompute ifl (fun xg yg -> 
        // upper bound
        let (_, rxg), (_, rxgb) = xg
        // low pass domain
        let rp = (ifl.NegInf, rxg), (Closed, rxgb)
        // intersection with second argument
        let res = intersectg_nc ifl rp yg
        res
        ) g h

    // apply high pass filter from first argument to second
    let highpassg ifl g h =
        if2GCompute ifl (fun xg yg -> 
        // lower bound
        let (lxg, _), (lxgb, _) = xg
        // high pass domain
        let rp = (lxg, ifl.PosInf), (lxgb, Closed)
        // intersection with second argument
        let res = intersectg_nc ifl rp yg
        res
        ) g h

    // Check if we have hit the dynamic range limits.
    let needmoreexpgQ env g =
        let ifl = env.ifl
        let glo, ghi = leftFloat g, rightFloat g
        let glob, ghib = leftInterval g,rightInterval g
        ((ghi = ifl.from -env.maxreal || glo = ifl.from -env.smallsubnormal) && glob) ||
        ((glo = ifl.from env.maxreal || ghi = ifl.from env.smallsubnormal) && ghib)

    let needmoreexpQ env ub = needmoreexpgQ env (ubound2g_nc env ub)

    // Find the relative width in a unum or ubound.
    let relwidthg (ifl : IFloat<'F>) g =
        let (|IsNaN|_|) x = if ifl.IsNaN x then Some IsNaN  else None
        let (|IsZero|_|) x = if x = ifl.Zero then Some IsZero  else None
        let (|IsInfinity|_|) x = if ifl.IsInf x then Some IsInfinity else None
        let glo, ghi = leftFloat g, rightFloat g
        match glo, ghi with
            | IsNaN, _  -> Double.PositiveInfinity
            | IsInfinity, _ |  _, IsInfinity -> 1.
            | IsZero, _ | _, IsZero -> 0.
            | _ -> ifl.float( ( Abs (Val ghi - Val glo) / (Abs (Val glo) + Abs (Val ghi)) ).Eval ifl )

    let relwidth env ub = relwidthg env.ifl (ubound2g_nc env ub)

    // Test if a larger fraction field is needed.
    let needmorefracQ env ub relwidthtolerance = relwidth env ub > relwidthtolerance

    // Increases the length of the exponent field of an exact unum u, if possible (preserving the numerical meaning).
    let promotee env u_ =
        ifExactUnumCompute env (fun u ->
        let e = expo_nc env u 
        let es = esize_nc env u
        let f = frac_nc env u
        let fs = fsize_nc env u
        let s = signmask_nc env u &&& u
        let ut = (env.utagmask &&& u) + uint64 env.fsizemax
        // If already maximum exponent size, do nothing. This also handles NaN and inf values
        if es = uint64 env.espmax then u
        // Take care of u = 0 case, ignoring the sign bit. It's simply the new utag.
        elif e = 0UL && f = 0UL then ut
        // If normal (nonzero exponent), slide sign bit left, add 2**(es-1), increment esize.
        elif e > 0UL then
            let hiddm = hiddenmask_nc env u
            (2UL * s) + ((e + uint64 ( pown 2 (int es - 1))) * hiddm) + ((hiddm - 1UL) &&& u) + uint64 env.fsizemax
        // Subnormal. Room to shift and stay subnormal?
        elif fs - (uint64 ( floor(log2 (float f)) ) + 1UL) >= uint64 ( pown 2 (int es - 1)) then
            (2UL * s) + (f * uint64 ( pown 2 (pown 2 (int es - 1)) ) * env.ulpu) + ut
        // Subnormal becomes normal. Trickiest case.
        // The fraction slides left such that the lefmost 1 becomes the hidden bit
        else
            let nsigbits = uint64 ( floor(log2 (float f)) ) + 1UL
            (2UL * s) + ( (uint64 ( pown 2 (int es - 1) ) + 1UL - fs + nsigbits) * (hiddenmask_nc env u) )
            + ( (f - uint64( pown 2 (int nsigbits) )) * uint64( pown 2 (int (fs - nsigbits + 1UL)) ) * env.ulpu ) + (env.utagmask &&& u) + uint64 env.fsizemax
        ) u_

    // appends 0 to fraction bits of an exact unum u, if possible (preserving the numerical meaning).
    let promotef env u_ = ifExactUnumCompute env (fun u -> if fsize_nc env u < uint64 env.fspmax then ( 2UL* (floatmask_nc env u &&& u) ) + (env.utagmask &&& u) + 1UL else u) u_

    // Finds a pair of unms that are equals to the exact unums u and v but have identical utags.
    // Promote a pair of exact unums to the same esize and fsize
    let promote env u_ v_ = 
        if2ExactUnumCompute env (fun u v ->
        let eu = esize_nc env u
        let ev = esize_nc env v
        let fu = fsize_nc env u
        let fv = fsize_nc env v
        // promote u exponent if needed
        let out1 = fWhile (fun (eu_,up) -> eu_ < ev)
                            (fun (eu_,up) -> (eu_ + 1UL, promotee env up) )
                            (eu, u)
        // else promote v exponent
        let out2 = fWhile (fun (ev_,vp) ->  ev_ < eu)
                            (fun (ev_,vp) -> (ev_ + 1UL, promotee env vp) )
                            (ev, v)
        // promote u fraction if needed
        let out3 = fWhile (fun (fu_,up) -> fu_ < fv)
                            (fun (fu_,up) -> (fu_ + 1UL, promotef env up) )
                            (fu, snd out1) // fu, new u
        // else promote v fraction
        let out4 = fWhile (fun (fv_,vp) -> fv_ < fu)
                            (fun (fv_,vp) -> (fv_ + 1UL, promotef env vp) )
                            (fv, snd out2) // new fu, new v
        // return promoted u and v
        snd out3, snd out4 // new u, new v
        ) u_ v_

    // Demote the fraction of a unum if possible,
    // even if it makes it inexact.
    let demotef env u_ =
        ifUnumCompute env (fun u ->
        // Cannot make the fraction any smaller
        if fsize_nc env u = 1UL || u = env.posinfu || u = env.neginfu || u = env.qNaNu || u = env.sNaNu then u
        // Else shift fraction right one bit.
        else ( (u &&& floatmask_nc env u) / 2UL ) ||| ( (env.utagmask &&& u) - 1UL )
        ) u_

    let fractionalPart x = let xa = abs x in xa - floor xa

    let integerPart x = let xa = abs x in floor xa

    let demotee env u_ =
        ifUnumCompute env (fun u ->
        let es = esize_nc env u
        let mask = (signmask_nc env u) / 4UL
        let fm = floatmask_nc env u
        let ut = u &&& env.utagmask
        let s = (signmask_nc env u) &&& u
        let f = frac_nc env u
        let left2 = (u &&& (3UL * mask)) / mask
        // Cannot make the exponent any smaller:
        if es = 1UL || u = env.posinfu || u = env.neginfu || u = env.qNaNu || u = env.sNaNu then u
        // Subnormal, so decreasing expo size means shifting fraction right by 2^2^(es-2) bits.
        elif expo_nc env u = 0UL then
            let f_ = (float f) / ( 2.**(2.**float(es-2UL)) )
            let ibit = if fractionalPart f_ > 0. then env.ubitmask else 0UL
            ibit ||| ((s / 2UL) + ( uint64 (integerPart f_) * env.ulpu ) + ut - uint64 env.fsizemax)
        // If the left two exponent bits are 00
        // (but it's normal, since we fell through the previous test),
        // result switches to subnormal. The exponent after the first
        // two bits joins the fraction like a fixed-point number,
        // before shifting the fraction to the right. The
        // new exponent is zero, of course.
        elif left2 = 0UL then
            let f_ = ((2.**float(fsize_nc env u)) + float f) / (2.**(-float(expo_nc env u) + (2.**float(es-2UL)) + 1.))
            let ibit = if fractionalPart f_ > 0. then env.ubitmask else 0UL
            ibit ||| ((s / 2UL) + (uint64 (integerPart f_) * env.ulpu) + ut - uint64 env.fsizemax)
        // If the left two exponent bits are 01 or 10,
        // squeeze out the second bit; if that leaves a subnormal exponent,
        // shift the hidden bit and fraction bits right
        elif left2 <= 2UL then
            let e = (((expomask_nc env u) - (3UL * mask)) &&& u) + ( (u &&& (2UL * mask)) / 2UL )
            let f_ = if e = 0UL then ((2.**float(fsize_nc env u)) + float f) / 2. else float f
            let ibit = if fractionalPart f_ > 0. then env.ubitmask else 0UL
            ibit ||| ((s / 2UL) + e + ((uint64 (integerPart f_)) * env.ulpu) + ut - uint64 env.fsizemax)
        // If the first two exponent bits are 11,
        // always get an unbounded unum, all 1s for fraction:
        else 
            ( (( (u &&& signmask_nc env u) + (fm - signmask_nc env u) ) / 2UL) ||| ut ) - uint64 env.fsizemax
        ) u_


    // Seek a single - ULP enclosure for a ubound greater than or equal to zero.
    let rec unifypos env ub =
        let ifl = env.ifl
        let u,v = match ub with | Unum(u_) -> u_, u_ | Bounds(u_, v_) -> u_, v_
        // First do trivial case where endpoints express the same value
        let ug = unum2g_nc env u
        let vg = unum2g_nc env v
        if ug = vg then g2u env ug
        // Cannot unify if the interval includes exact 0, 1, 2, or 3
        else if nnequQ_nc env ub (Unum env.zerou) || nnequQ_nc env ub (Unum env.oneu) || nnequQ_nc env ub (Unum env.twou) || nnequQ_nc env ub (Unum env.threeu) then ub
        // Refine the endpoints for the tightest possible unification.
        else
            let (ugL,_),_ = ug 
            let ugLu = x2u env ugL
            let up0 = fst ( promote env ugLu env.efsizevalmax )
            let up = (if inexQ_nc env u then up0 + env.ubitmask else up0 - env.ubitmask)
            let (_,vgR),_ = vg
            let vgRu = x2u env vgR
            let vp0 = fst ( promote env vgRu env.efsizevalmax )
            let vp = (if inexQ_nc env v then vp0 - env.ubitmask else vp0 + env.ubitmask)
            if up = vp then Unum up
            // If upper bound is open infinty and lower bound > maxreal, special handling is needed
            else
            let (_,vpgR), (_,vpgB) = unum2g_nc env vp
            if vpgR = ifl.PosInf && vpgB then
                if ltuQ env (Unum(env.maxrealu)) (Unum up) then Unum (env.maxrealu + env.ubitmask)
                // Demote the left bound until the upper bound is open infinity
                else
                    let ud = fWhile ( fun u_-> rightFloat (unum2g_nc env u_) < ifl.PosInf )
                                (fun u_ -> if esize_nc env u_ > 1UL then demotee env u_ else demotef env u_ ) up
                    Unum ud
            // While demoting exponents is possible and still leaves unums within ubound, demote both exponents
            else
                let up1, vp1, _, _ =
                    fWhile ( fun (u_, v_, ud_, vd_) -> 
                        if u_ = v_ then
                            false
                        else
                            let (udgL, udgR),_ = unum2g_nc env ud_
                            let (vdgL, vdgR),_ = unum2g_nc env vd_
                            udgL < vdgL && udgR < vdgR && vdgR < ifl.PosInf && (esize_nc env u_) > 1UL )
                        ( fun (u_, v_, ud_, vd_) -> ud_, vd_, demotee env ud_, demotee env vd_ )
                        (up, vp, demotee env up, demotee env vp)
                let up2, vp2 = fWhile (fun (u_, v_) -> u_ <> v_ && (frac_nc env v_ <> frac_nc env u_) && (fsize_nc env u_) > 1UL )
                                      (fun (u_, v_) -> demotef env u_, demotef env v_ ) (up1, vp1)
                // If u is inexact zero and v < 1, a little special handling is needed.
                if up2 <> vp2 && ((floatmask_nc env up2 + env.ubitmask) ||| up2) = env.ubitmask && (ltuQ env (Unum(vp2)) (Unum(env.oneu))) then
                    let nvp2 = vp2 + (if (exQ env vp2) then env.ubitmask else 0UL)
                    let (_,nvp2R),_ = unum2g_nc env nvp2
                    let n = min env.espmax (int (floor (ifl.float (ifl.log2 (ifl.minuslfloat (1., ifl.log2 nvp2R))))))
                    Unum ( x2u env (ifl.from (2.**(-2.**float n + 1.))) - env.ubitmask )
                elif up2 = vp2 then Unum(up2) else ub

    and negateu env = function | Unum u -> if unum2g_nc env u = unum2g_nc env 0UL then Unum (env.zerou) else Unum ((signmask_nc env u) ^^^ u)
                               | Bounds (u, v) -> Bounds ( (if unum2g_nc env v = unum2g_nc env 0UL then env.zerou else (signmask_nc env v) ^^^ v),
                                                           (if unum2g_nc env u = unum2g_nc env 0UL then env.zerou else (signmask_nc env u) ^^^ u)  )

    and unify env ub =
        let u, v = match ub with | Unum(u_) -> u_, u_ | Bounds(u_, v_) -> u_, v_
        if u = env.qNaNu || u = env.sNaNu || v = env.qNaNu || v = env.sNaNu then Unum env.qNaNu
        elif u = env.posinfu && v = env.posinfu then Unum env.posinfu
        elif u = env.neginfu && v = env.neginfu then Unum env.neginfu
        else
        let zero = Unum (env.zerou)
        if u = env.neginfu || u = env.posinfu || v = env.neginfu || v = env.posinfu ||
             ( ltuQ env (Unum u) zero && not (ltuQ env (Unum v) zero) ) then ub
        elif ltuQ env (Unum u) zero && ltuQ env (Unum v) zero then negateu env (unifypos env (negateu env ub) )
        elif unum2g_nc env u = unum2g_nc env v then Unum (min u v)
        else unifypos env ub

    // Find the left half of a ubound (numerical value and open-closed)
    and ubleft env xleft bleft u =
        let ifl = env.ifl
        if xleft = ifl.NegInf then if bleft then env.negopeninfu else env.neginfu
        elif u2f_nc env (exact_nc env u) =  xleft then if bleft then ( u - (env.ulpu * BooleU ( xleft < ifl.Zero )) ) ||| env.ubitmask else u
        else u ||| (BooleU bleft * env.ubitmask)
            
    // Find the right half of a ubound (numerical value and open-closed)
    // Not exactly the reverse of ubleft, because of "negative zero".
    and ubright env xright bright u =
        let ifl = env.ifl
        if xright = ifl.PosInf then if bright then env.posopeninfu else env.posinfu
        elif xright = ifl.Zero && bright then env.negopenzerou
        elif u2f_nc env (exact_nc env u) = xright then if bright then ( u - (env.ulpu * BooleU ( xright >= ifl.Zero )) ) ||| env.ubitmask else u
        else u ||| (BooleU bright * env.ubitmask)

    and g2u env g =
        let ((flo,fhi),(blo,bhi)) = g
        let ulo, uhi = x2u env flo, x2u env fhi
        if ulo = env.qNaNu || uhi = env.qNaNu || (flo > fhi) || ( flo = fhi && (blo || bhi) ) then Unum env.qNaNu
        elif ulo = uhi && blo = bhi then Unum ulo 
        else
        let u1 = ubleft env flo blo ulo
        let u2 = ubright env fhi bhi uhi
        let ub_u1u2 = Bounds (u1, u2)
        let unify_u1u2 = unify env ub_u1u2
        if ubound2g_nc env unify_u1u2 = ubound2g_nc env ub_u1u2 then unify_u1u2 else ub_u1u2

    // Intersect two ubounds or unums.
    let intersectu env ub_ vb_ = if2UboundCompute env (fun ub vb -> g2u env (intersectg env.ifl (ubound2g env ub) (ubound2g env vb))) ub_ vb_

    type datamoved =
        {ubitsmoved : int; numbersmoved: int}
        static member Zero = {ubitsmoved = 0; numbersmoved = 0}
        static member (+) (lhs : datamoved, rhs : datamoved) = {ubitsmoved = lhs.ubitsmoved + rhs.ubitsmoved; numbersmoved = lhs.numbersmoved + rhs.numbersmoved}

    let nbits env = function | Unum u -> 1 + numbits env u | Bounds (u, v) -> 1 + numbits env u +  numbits env v

    let plusu env dmoved ub vb =
        if2UboundCompute env ( fun x y -> 
        let sum = plusg env.ifl (ubound2g_nc env x) (ubound2g_nc env y) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) ->   Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env vb + nbits env sum;
                                              numbersmoved = dm.numbersmoved + 3 }
                        | None -> None
        datamoved, sum
        ) ub vb 

    let negateg (ifl : IFloat<_>) x = let ((xlo, xhi),(blo, bhi)) = x in ((ifl.negate xhi, ifl.negate xlo),(bhi, blo))

    let minusg ifl x y = plusg ifl x (negateg ifl y)

    let minusu env dmoved ub vb =
        if2UboundCompute env ( fun x y -> 
        let sub = minusg env.ifl (ubound2g_nc env x) (ubound2g_nc env y) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env vb + nbits env sub;
                                            numbersmoved = dm.numbersmoved + 3 }
                        | None -> None
        datamoved, sub
        ) ub vb 

    // The "left" multiplication table for general intervals.
    let timesposleft (ifl : IFloat<_>) x_ y_ =
        let x, xb = x_
        let y, yb = y_
        if x_ = (ifl.Zero, Closed) then if y_ = (ifl.PosInf, Closed) then ifl.NaN, Open else ifl.Zero, Closed
        elif y_ = (ifl.Zero, Closed) then if x_ = (ifl.PosInf, Closed) then ifl.NaN, Open else ifl.Zero, Closed
        elif x_ = (ifl.Zero, Open) then if y_ = (ifl.PosInf, Closed) then ifl.PosInf, Closed else ifl.Zero, Open
        elif y_ = (ifl.Zero, Open) then if x_ = (ifl.PosInf, Closed) then ifl.PosInf, Closed else ifl.Zero, Open
        elif x_ = (ifl.PosInf, Closed) || y_ = (ifl.PosInf, Closed) then (ifl.PosInf, Closed)
        else ifl.times(x, y), xb || yb

    // The "right" multiplication table for general intervals.
    let timesposright (ifl : IFloat<_>) x_ y_ =
        let x, xb = x_
        let y, yb = y_
        if x_ = (ifl.PosInf, Closed) then if y_ = (ifl.Zero, Closed) then ifl.NaN, Open else ifl.PosInf, Closed
        elif y_ = (ifl.PosInf, Closed) then if x_ = (ifl.Zero, Closed) then ifl.NaN, Open else ifl.PosInf, Closed
        elif x_ = (ifl.PosInf, Open) then if y_ = (ifl.Zero, Closed) then ifl.Zero, Closed else ifl.PosInf, Open
        elif y_ = (ifl.PosInf, Open) then if x_ = (ifl.Zero, Closed) then ifl.Zero, Closed else ifl.PosInf, Open
        elif x_ = (ifl.Zero, Closed) || y_ = (ifl.Zero, Closed) then (ifl.Zero, Closed)
        else ifl.times(x, y), xb || yb

    // Helper function for times; negates numerical part of an endpoint.
    let neg (ifl : IFloat<_>) x = let x, xb = x in ifl.negate x, xb

    let timesg (ifl : IFloat<_>) x y =
        let ((xlo, xhi), (xlob, xhib)) = x
        let ((ylo, yhi), (ylob, yhib)) = y
        // If any value is NaN, the result is also NaN.
        if  ifl.IsNaN xlo || ifl.IsNaN xhi || ifl.IsNaN ylo || ifl.IsNaN yhi then (ifl.NaN, ifl.NaN), (Open, Open)
        else
            let lcan = [// Lower left corner is in upper right quadrant, facing uphill:
                        if xlo >= ifl.Zero && ylo >= ifl.Zero then yield timesposleft ifl (xlo, xlob) (ylo, ylob)
                        // Upper right corner is in lower left quadrant, facing uphill:
                        if (xhi < ifl.Zero || (xhi = ifl.Zero && xhib)) && (yhi < ifl.Zero || (yhi = ifl.Zero && yhib)) then yield timesposleft ifl (ifl.negate xhi, xhib) (ifl.negate yhi, yhib)
                        // Upper left corner is in upper left quadrant, facing uphill:
                        if (xlo < ifl.Zero || (xlo = ifl.Zero && not xlob)) && (yhi > ifl.Zero || (yhi = ifl.Zero && not yhib)) then yield neg ifl <| timesposright ifl (ifl.negate xlo, xlob) (yhi, yhib)
                        // Lower right corner is in lower right quadrant, facing uphill:
                        if (xhi > ifl.Zero || (xhi = ifl.Zero && not xhib)) && (ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) then yield neg ifl <| timesposright ifl (xhi, xhib) (ifl.negate ylo, ylob) ]
            let rcan = [// Upper right corner is in upper right quadrant, facing downhill:
                        if (xhi > ifl.Zero || (xhi = ifl.Zero && not xhib)) && (yhi > ifl.Zero || (yhi = ifl.Zero && not yhib)) then yield timesposright ifl (xhi, xhib) (yhi, yhib)
                        // Lower left corner is in lower left quadrant, facing downhill:
                        if (xlo < ifl.Zero || (xlo = ifl.Zero && not xlob)) && (ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) then yield timesposright ifl (ifl.negate xlo, xlob) (ifl.negate ylo, ylob)
                        // Lower right corner is in upper left quadrant, facing downhill:
                        if (xhi < ifl.Zero || (xhi = ifl.Zero && xhib)) && ylo >= ifl.Zero then yield neg ifl <| timesposleft ifl (ifl.negate xhi, xhib) (ylo, ylob) // ERROR: timesright in unum.py
                        // Upper left corner is in lower right quadrant, facing downhill:
                        if xlo >= ifl.Zero && (yhi < ifl.Zero || (yhi = ifl.Zero && yhib)) then yield neg ifl <| timesposleft ifl (xlo, xlob) (ifl.negate yhi, yhib) ] // ERROR: timesright in unum.py
            if List.exists (fun hg -> ifl.IsNaN <| fst hg) lcan || List.exists (fun hg -> ifl.IsNaN <| fst hg) rcan then (ifl.NaN, ifl.NaN), (Open, Open)
            else
                let lcansorted = List.sort lcan
                let rcansorted = List.sort rcan
                let l0 , l1 = match lcansorted with | f :: s :: t -> Some f, Some s | f :: _ -> Some f, None | _ -> None, None // last case impossible (at least 1 item)
                let timesleft, openleft_ = l0.Value
                let rlast, rlastm1 = match List.rev rcansorted with | last :: lm1 :: tr -> Some last, Some lm1 | last :: t -> Some last, None | _ -> None, None
                let timesright, openright_ = rlast.Value
                // if the either two ending elements are numerically identical, the Closed interval must win
                let openleft = if l1.IsSome && timesleft = fst l1.Value && (not openleft_ || not (snd l1.Value)) then Closed else openleft_
                let openright = if rlastm1.IsSome && timesright = fst rlastm1.Value && (not openright_ || not (snd rlastm1.Value)) then Closed else openright_
                (timesleft, timesright), (openleft, openright)

    let timesu env dmoved ub vb =
        if2UboundCompute env ( fun x y -> 
        let mult = timesg env.ifl (ubound2g_nc env x) (ubound2g_nc env y) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env vb + nbits env mult;
                                            numbersmoved = dm.numbersmoved + 3 }
                        | None -> None
        datamoved, mult
        ) ub vb 

    // The "left" division table for general intervals.
    let divideposleft (ifl : IFloat<_>) x_ y_ =
        let x, xb = x_
        let y, yb = y_
        if y_ = (ifl.Zero, Closed) then ifl.NaN, Open 
        elif x_ = (ifl.PosInf, Closed) then if y_ = (ifl.PosInf, Closed) then ifl.NaN, Open else ifl.PosInf, Closed
        elif x_ = (ifl.Zero, Closed) || y_ = (ifl.PosInf, Closed) then (ifl.Zero, Closed)
        elif x_ = (ifl.Zero, Open) || y_ = (ifl.PosInf, Open) then (ifl.Zero, Open)
        else ifl.divides(x, y), xb || yb

    // The "right" division table for general intervals.
    let divideposright (ifl : IFloat<_>) x_ y_ =
        let x, xb = x_
        let y, yb = y_
        if y_ = (ifl.Zero, Closed) then ifl.NaN, Open 
        elif x_ = (ifl.PosInf, Closed) then if y_ = (ifl.PosInf, Closed) then ifl.NaN, Open else ifl.PosInf, Closed
        elif x_ = (ifl.Zero, Closed) || y_ = (ifl.PosInf, Closed) then (ifl.Zero, Closed)
        elif x_ = (ifl.PosInf, Open) || y_ = (ifl.Zero, Open) then (ifl.PosInf, Open)
        else ifl.divides(x, y), xb || yb

    // Division in the g - layer.
    let divideg (ifl : IFloat<_>) x y =
        let ((xlo, xhi), (xlob, xhib)) = x
        let ((ylo, yhi), (ylob, yhib)) = y
        // If any value is NaN, or denominator contains 0, the result is a NaN.
        if  (ifl.IsNaN xlo || ifl.IsNaN xhi || ifl.IsNaN ylo || ifl.IsNaN yhi) ||
            ((ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) && (yhi > ifl.Zero || (yhi = ifl.Zero && not yhib))) then (ifl.NaN, ifl.NaN), (Open, Open)
        else
            let lcan = [// Upper left corner is in upper right quadrant, facing uphill:
                        if xlo >= ifl.Zero && ( yhi > ifl.Zero || (yhi = ifl.Zero && not yhib) ) then yield divideposleft ifl (xlo, xlob) (yhi, yhib)
                        // Lower right corner is in lower left quadrant, facing uphill:
                        if (xhi < ifl.Zero || (xhi = ifl.Zero && xhib)) && (ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) then yield divideposleft ifl (ifl.negate xhi, xhib) (ifl.negate ylo, ylob)
                        // Lower left corner is in upper left quadrant, facing uphill:
                        if (xlo < ifl.Zero || (xlo = ifl.Zero && not xlob)) && ylo >= ifl.Zero then yield neg ifl <| divideposright ifl (ifl.negate xlo, xlob) (ylo, ylob)
                        // Upper right corner is in lower right quadrant, facing uphill:
                        if (xhi > ifl.Zero || (xhi = ifl.Zero && not xhib)) && (yhi < ifl.Zero || (yhi = ifl.Zero && yhib)) then yield neg ifl<| divideposright ifl (xhi, xhib) (ifl.negate yhi, yhib) ]
            let rcan = [// Lower right corner is in upper right quadrant, facing downhill:
                        if (xhi > ifl.Zero || (xhi = ifl.Zero && not xhib)) && ylo >= ifl.Zero then yield divideposright ifl (xhi, xhib) (ylo, ylob)
                        // Upper left corner is in lower left quadrant, facing downhill:
                        if (xlo < ifl.Zero || (xlo = ifl.Zero && not xlob)) && (yhi < ifl.Zero || (yhi = ifl.Zero && yhib)) then yield divideposright ifl (ifl.negate xlo, xlob) (ifl.negate yhi, yhib)
                        // Upper right corner is in upper left quadrant, facing downhill:
                        if (xhi < ifl.Zero || (xhi = ifl.Zero && xhib)) && (yhi > ifl.Zero || (yhi = ifl.Zero && not yhib)) then yield neg ifl <| divideposleft ifl (ifl.negate xhi, xhib) (yhi, yhib)
                        // Lower left corner is in lower right quadrant, facing downhill:
                        if xlo >= ifl.Zero && (ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) then yield neg ifl<| divideposleft ifl (xlo, xlob) (ifl.negate ylo, ylob) ]
            if List.exists (fun hg -> ifl.IsNaN <| fst hg) lcan || List.exists (fun hg -> ifl.IsNaN <| fst hg) rcan then
                (ifl.NaN, ifl.NaN), (Open, Open)
            else
                let lcansorted = List.sort lcan
                let rcansorted = List.sort rcan
                let l0 , l1 = match lcansorted with | f :: s :: t -> Some f, Some s | f :: _ -> Some f, None | _ -> None, None // last case impossible (at least 1 item)
                let divleft, openleft_ = l0.Value
                let rlast, rlastm1 = match List.rev rcansorted with | last :: lm1 :: tr -> Some last, Some lm1 | last :: t -> Some last, None | _ -> None, None
                let divright, openright_ = rlast.Value
                // if the either two ending elements are numerically identical, the Closed interval must win
                let openleft = if l1.IsSome && divleft = fst l1.Value && (not openleft_ || not (snd l1.Value)) then Closed else openleft_
                let openright = if rlastm1.IsSome && divright = fst rlastm1.Value && (not openright_ || not (snd rlastm1.Value)) then Closed else openright_
                (divleft, divright), (openleft, openright)

    let divideu env dmoved ub vb =
        if2UboundCompute env ( fun x y -> 
        let div = divideg env.ifl (ubound2g_nc env x) (ubound2g_nc env y) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env vb + nbits env div;
                                            numbersmoved = dm.numbersmoved + 3 }
                        | None -> None
        datamoved, div
        ) ub vb 

    let squareg (ifl : IFloat<_>) g =
        let (g1, g2), (b1, b2) = g
        if ifl.IsNaN g1 || ifl.IsNaN g2 then (ifl.NaN, ifl.NaN), (Open, Open)
        else
            let t1, t2 = ifl.times( g1, g1 ), ifl.times( g2, g2 )
            let tset = List.sort [(t1, b1); (t2, b2)]
            let (t1_, b1_), (t2_, b2_) = List.head tset, List.last tset
            if (g1 < ifl.Zero && g2 > ifl.Zero) || (g1 > ifl.Zero && g2 < ifl.Zero) || (g1 = ifl.Zero && not b1) || (g2 = ifl.Zero && not b2) then
                if t1 = t2 then (ifl.Zero, t1), (Closed, b1 && b2) else (ifl.Zero, t2_), (Closed, b2_)
            else (t1_, t2_), (b1_, b2_)

    // Square in the u - layer, with tallying of bits and numbers moved.
    let squareu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let sq = squareg env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env sq;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, sq
        ) ub

    // Square root in the g - layer.
    let sqrtg (ifl : IFloat<_>) g =
        let (g1, g2), (b1, b2) = g
        if ifl.IsNaN g1 || ifl.IsNaN g2 || (g1 < ifl.Zero) then (ifl.NaN, ifl.NaN), (Open, Open) else (ifl.sqrt g1, ifl.sqrt g2), (b1, b2)

    // Square root in the u - layer, with tallying of bits and numbers moved.
    let sqrtu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let sqrt = sqrtg env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env sqrt;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, sqrt
        ) ub

    // The "left" power function tables for general intervals.
    let powposleft (ifl : IFloat<_>) x_  y_ =
        let x, xb = x_
        let y, yb = y_
        if x >= ifl.One && y >= ifl.Zero then
            if x_ = (ifl.One, Closed) then if y_ = (ifl.PosInf, Closed) then ifl.NaN, Open else ifl.One, Closed
            elif y_ = (ifl.Zero, Closed) then if x_ = (ifl.PosInf, Closed) then ifl.NaN, Open else ifl.One, Closed
            elif x_ = (ifl.One, Open) then if y_ = (ifl.PosInf, Closed) then ifl.PosInf, Closed else ifl.One, Open
            elif y_ = (ifl.Zero, Open) then if x_ = (ifl.PosInf, Closed) then ifl.PosInf, Closed else ifl.One, Open
            elif x_ = (ifl.PosInf, Closed) || y_ = (ifl.PosInf, Closed) then ifl.PosInf, Closed
            else ifl.Pow(x,y), xb || yb
        else failwith <| sprintf "ERROR: pow invalid arguments %s^%s" (ifl.sprint x) (ifl.sprint y)

    // The "right" power function tables for general intervals.
    let powposright (ifl : IFloat<_>) x_ y_ =
        let x, xb = x_
        let y, yb = y_
        if x >= ifl.One && y >= ifl.Zero then
            if x_ = (ifl.PosInf, Closed) then if y_ = (ifl.Zero, Closed) then ifl.NaN, Open else ifl.PosInf, Closed
            elif y_ = (ifl.PosInf, Closed) then if x_ = (ifl.One, Closed) then ifl.NaN, Open else ifl.PosInf, Closed
            elif x_ = (ifl.PosInf, Open) then if y_ = (ifl.Zero, Closed) then ifl.One, Closed else ifl.PosInf, Open
            elif y_ = (ifl.PosInf, Open) then if x_ = (ifl.One, Closed) then ifl.One, Closed else ifl.PosInf, Open
            elif x_ = (ifl.One, Closed) || y_ = (ifl.Zero, Closed) then ifl.One, Closed
            else ifl.Pow(x,y), xb || yb
        else failwith <| sprintf "ERROR: pow invalid arguments %s^%s" (ifl.sprint x) (ifl.sprint y)

    // Reciprocal helper function for the power function.
    let recip (ifl : IFloat<_>) x =
        if ifl.IsNaN (fst x)  then ifl.NaN, Open
        elif fst x = ifl.Zero then ifl.PosInf, snd x
        else ifl.divideslfloat (1., fst x), snd x

    let EvenQ (ifl : IFloat<_>) x =
        let q = ( Floor( Val x / 2. ) ).Eval ifl
        (Val x - Val q * 2.).Eval ifl = ifl.Zero

    // Power function in the g - layer.
    let powg (ifl : IFloat<_>) x y =
        let ((xlo, xhi), (xlob, xhib)) = x
        let ((ylo, yhi), (ylob, yhib)) = y
        // If any value is NaN, the result is also NaN.
        if ifl.IsNaN xlo || ifl.IsNaN xhi || ifl.IsNaN ylo || ifl.IsNaN yhi then (ifl.NaN, ifl.NaN), (Open, Open)
        // Do not allow exact zero to a negative or zero power, unless the negative power is an exact even integer.
        elif (xlo < ifl.Zero || (xlo = ifl.Zero && not xlob)) && (xhi > ifl.Zero || (xhi = ifl.Zero && not xhib)) &&
             (ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) && not (ylo = yhi && ylo < ifl.Zero && EvenQ ifl ylo) then (ifl.NaN, ifl.NaN), (Open, Open)
        // Weird case: complex number of zero magnitude is real. Zero.
        elif yhi = ifl.NegInf && not yhib && ((xlo > ifl.One || (xlo = ifl.One && xlob))||(xhi < ifl.One || (xhi = ifl.One && xhib))) then (ifl.Zero, ifl.Zero), (Closed, Closed)
        // If y is an exact integer, loads of special cases.
        elif ylo = yhi && not ylob && not yhib && IsInteger ifl ylo then
            // Finite nonzero numbers to the power 0 equals 1.
            if ylo = ifl.Zero then
                if (xlo > ifl.Zero || (xlo = ifl.Zero && xlob)) && (xhi < ifl.PosInf || (xhi = ifl.PosInf && xhib)) ||
                   (xlo > ifl.NegInf || (xlo = ifl.NegInf && xlob)) && (xhi = ifl.Zero && xhib) then (ifl.One, ifl.One), (Closed, Closed) else (ifl.NaN, ifl.NaN), (Open, Open)
            // Positive even power is like square function; test for zero straddle.
            elif EvenQ ifl ylo && ylo > ifl.Zero then
                // Range is strictly negative. Order of endpoints reverses.
                if xhi < ifl.Zero || (xhi = ifl.Zero && xhib) then (ifl.Pow(xhi,ylo), ifl.Pow(xlo,ylo)), (xhib, xlob)
                // Range is strictly positive. Endpoints preserve ordering.
                elif xlo > ifl.Zero || (xlo = ifl.Zero && xlob) then (ifl.Pow(xlo,ylo), ifl.Pow(xhi,ylo)), (xlob, xhib)
                // Range straddles zero. Closed zero is lower bound. Larger x^y is upper bound, but beware of ties between open and closed.
                else
                    let t1, t2 = ifl.Pow(xlo,ylo), ifl.Pow(xhi,ylo)
                    if t1 < t2 then (ifl.Zero, t2),(Closed, xhib) elif t1 > t2 then (ifl.Zero, t1),(Closed, xlob) else (ifl.Zero, t1),(Closed, xlob && xhib)
            // Negative even power includes + Infinity if zero straddle.
            elif EvenQ ifl ylo && ylo < ifl.Zero then
                // Range is strictly positive. Order of endpoints reverses.
                if xlo > ifl.Zero || (xlo = ifl.Zero && xlob) then (ifl.Pow(xhi,ylo), if xlo = ifl.Zero then ifl.PosInf else ifl.Pow(xlo,ylo)), (xhib, xlob)
                // Range is strictly negative. Endpoints preserve ordering.
                elif xhi < ifl.Zero || (xhi = ifl.Zero && xhib) then (ifl.Pow(xlo,ylo), if xhi = ifl.Zero then ifl.PosInf else ifl.Pow(xhi,ylo)), (xlob, xhib)
                // Range straddles zero. Closed infinity is upper bound. smaller x^y is lower bound, but beware of ties between open and closed.
                else
                    let t1 = if xlo = ifl.Zero && ylo < ifl.Zero then ifl.PosInf else ifl.Pow(xlo,ylo)
                    let t2 = if xhi = ifl.Zero && ylo < ifl.Zero then ifl.PosInf else ifl.Pow(xhi,ylo)
                    if t1 > t2 then (t2, ifl.PosInf), (xhib, Closed) elif t1 < t2 then (t1, ifl.PosInf), (xlob, Closed) else (t1, ifl.PosInf), (xlob && xhib, Closed)
            // That leaves odd integer powers. Preserves ordering if positive.
            elif ylo > ifl.Zero then (ifl.Pow(xlo,ylo), ifl.Pow(xhi,ylo)), (xlob, xhib)
            // Negative odd power. Reverses ordering.
            else ((if xhi = ifl.Zero then ifl.NegInf else ifl.Pow(xhi,ylo)), (if xlo = ifl.Zero then ifl.PosInf else ifl.Pow(xlo,ylo)) ), (xhib, xlob)
        // Otherwise, negative x not allowed.
        elif xlo < ifl.Zero then (ifl.NaN, ifl.NaN), (Open, Open)
        // Non-integer exponent, and x is nonnegative. Find candidates.
        else
            let lcan = [// Lower left corner is in upper right quadrant, facing uphill:
                        if xlo >= ifl.One && ylo >= ifl.Zero then yield powposleft ifl (xlo, xlob) (ylo, ylob)
                        // Upper right corner is in lower left quadrant, facing uphill:
                        if (xhi < ifl.One || (xhi = ifl.One && xhib)) && (yhi < ifl.Zero || (yhi = ifl.Zero && yhib)) then yield powposleft ifl (recip ifl (xhi, xhib)) (ifl.negate yhi, yhib) 
                        // Upper left corner is in upper left quadrant, facing uphill:
                        if (xlo < ifl.One || (xlo = ifl.One && not xlob)) && (yhi > ifl.Zero || (yhi = ifl.Zero && not xhib)) then yield recip ifl <| powposright ifl (recip ifl (xlo, xlob)) (yhi, yhib)
                        // Lower right corner is in lower right quadrant, facing uphill:
                        if (xhi > ifl.One || (xhi = ifl.Zero && not xhib)) && (ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) then yield recip ifl <| powposright ifl (xhi, xhib) (ifl.negate ylo, ylob) ]
            let rcan = [// Upper right corner is in upper right quadrant, facing downhill:
                        if (xhi > ifl.One || (xhi = ifl.One && not xhib)) && (yhi > ifl.Zero || (yhi = ifl.Zero && not yhib)) then yield powposright ifl (xhi, xhib) (yhi, yhib)
                        // Lower left corner is in lower left quadrant, facing downhill:
                        if (xlo < ifl.One || (xlo = ifl.One && not xlob) ) && (ylo < ifl.Zero || (ylo = ifl.Zero && not ylob)) then yield powposright ifl (recip ifl (xlo, xlob)) (ifl.negate ylo, ylob)
                        // Lower right corner is in upper left quadrant, facing downhill:
                        if (xhi < ifl.One || (xhi = ifl.One && xhib)) && ylo >= ifl.Zero then yield recip ifl <| powposleft ifl (recip ifl (xhi, xhib)) (ylo, ylob)
                        // Upper left corner is in lower right quadrant, facing downhill:
                        if xlo >= ifl.One && ( yhi < ifl.Zero || (yhi = ifl.Zero && yhib)) then yield recip ifl <| powposleft ifl (xlo, xlob) (ifl.negate yhi, yhib) ]
            if List.exists (fun hg -> ifl.IsNaN <| fst hg) lcan || List.exists (fun hg -> ifl.IsNaN <| fst hg) rcan then
                (ifl.NaN, ifl.NaN), (Open, Open)
            else
                let lcansorted = List.sort lcan
                let rcansorted = List.sort rcan
                let l0 , l1 = match lcansorted with | f :: s :: t -> Some f, Some s | f :: _ -> Some f, None | _ -> None, None // last case impossible (at least 1 item)
                let powleft, openleft_ = l0.Value
                let rlast, rlastm1 = match List.rev rcansorted with | last :: lm1 :: tr -> Some last, Some lm1 | last :: t -> Some last, None | _ -> None, None
                let powright, openright_ = rlast.Value
                // if the either two ending elements are numerically identical, the Closed interval must win
                let openleft = if l1.IsSome && powleft = fst l1.Value && (not openleft_ || not (snd l1.Value)) then Closed else openleft_
                let openright = if rlastm1.IsSome && powright = fst rlastm1.Value && (not openright_ || not (snd rlastm1.Value)) then Closed else openright_
                (powleft, powright), (openleft, openright)

    let powu env dmoved ub vb =
        if2UboundCompute env ( fun x y -> 
        let pow = powg env.ifl (ubound2g_nc env x) (ubound2g_nc env y) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env vb + nbits env pow;
                                            numbersmoved = dm.numbersmoved + 3 }
                        | None -> None
        datamoved, pow
        ) ub vb

    // Exponential function in the g-layer.
    let  expg env g =
        let ifl = env.ifl
        let (g1, g2), (b1, b2) = g
        let lo = (Log (From env.smallsubnormal)).Eval ifl
        let hi = (Log (From env.maxreal)).Eval ifl
        let glo = if ifl.IsNaN g1 || ifl.IsNaN g2 then ifl.NaN, Open
                  elif g1 = ifl.NegInf && not b1 then ifl.Zero, Closed
                  elif g1 = ifl.Zero && not b1 then ifl.One, Closed
                  elif g1 = ifl.PosInf && not b1 then ifl.PosInf, Closed
                  elif g1 < lo then ifl.Zero, Open
                  elif g1 > hi then ifl.from env.maxreal, Open
                  else ifl.exp g1, Open
        let ghi = if ifl.IsNaN g2 || ifl.IsNaN g2 then ifl.NaN, Open
                  elif g2 = ifl.NegInf && not b2 then ifl.Zero, Closed
                  elif g2 = ifl.Zero && not b2 then ifl.One, Closed
                  elif g2 = ifl.PosInf && not b2 then ifl.PosInf, Closed
                  elif g2 < lo then ifl.from env.smallsubnormal, Open
                  elif g2 > hi then ifl.PosInf, Open
                  else ifl.exp g2, Open
        if fst glo = fst ghi then (fst glo, fst glo), (Closed, Closed) else (fst glo, fst ghi), (snd glo, snd ghi)
    
    // Exponential function in the u-layer, with tallying of bits and numbers moved.
    let expu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let expo = expg env (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env expo;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, expo
        ) ub

    // Absolute value in the g-layer.
    let absg (ifl : IFloat<_>) g = 
        let (g1, g2), (b1, b2) = g
        if ifl.IsNaN g1 || ifl.IsNaN g2 then (ifl.NaN, ifl.NaN), (Open, Open)
        elif g2 <= ifl.Zero then (ifl.abs g2, ifl.abs g1), (b2, b1)
        elif g1 <= ifl.Zero then
            if ifl.abs g1 < ifl.abs g2 then (ifl.Zero, ifl.abs g2), (Closed, b2)
            elif ifl.abs g1 > ifl.abs g2 then  (ifl.Zero, ifl.abs g1), (Closed, b1)
            else (ifl.Zero, ifl.abs g2), (Closed, b1 && b2)
        else (ifl.abs g1, ifl.abs g2), (b1, b2)

    // Absolute value in the u-layer, with tallying of bits and numbers moved.
    let absu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let abso = absg env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env abso;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, abso
        ) ub

    // Logarithm in the g-layer.
    let logg (ifl : IFloat<_>) g =
        let (g1, g2), (b1, b2) = g
        if ifl.IsNaN g1 || ifl.IsNaN g2 then (ifl.NaN, ifl.NaN), (Open, Open)
        elif g1 < ifl.Zero || (g1 = ifl.Zero && b1) then (ifl.NaN, ifl.NaN), (Open, Open)
        else
            let glo = if g1 = ifl.Zero && not b1 then ifl.NegInf, Closed
                      elif g1 = ifl.One && not b1 then ifl.Zero, Closed
                      elif g1 = ifl.PosInf && not b1 then ifl.PosInf, Closed
                      else ifl.log g1, Open
            let ghi = if g2 = ifl.Zero && not b2 then ifl.NegInf, Closed
                      elif g2 = ifl.One && not b2 then ifl.Zero, Closed
                      elif g2 = ifl.PosInf && not b2 then ifl.PosInf, Closed
                      else ifl.log g2, Open
            if g1 = g2 then f2g ifl <| ifl.log g1 else (fst glo, fst ghi), (snd glo, snd ghi)

    // Logarithm in the u-layer, with tallying of bits and numbers moved.
    let logu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let loga = logg env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env loga;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, loga
        ) ub

    //let cosdeg (ifl : IFloat<_>) x = ifl.cos (ifl.times( ifl.dividesrfloat (x, 180.), ifl.Pi))
    let cosdeg (ifl : IFloat<_>) x = ( Cos ( Val x * Val ifl.Pi / 180. ) ).Eval ifl

    // Cosine in the g-layer.
    let cosg (ifl : IFloat<_>) g =
        let (g1, g2), (b1, b2) = g
        if ifl.IsNaN g1 || ifl.IsNaN g2 then (ifl.NaN, ifl.NaN), (Open, Open)
        elif g1 = ifl.PosInf || g2 = ifl.PosInf || g1 = ifl.NegInf || g2 = ifl.NegInf then (ifl.MinusOne, ifl.One), (Closed, Closed)
        elif ifl.float (ifl.minus( g2, g1 )) > 360. then (ifl.MinusOne, ifl.One), (Closed, Closed)
        else
            // Translate g1 and g2 so g1 is in [0,360). This also assures that g2 is in [0,720], because of the previous If test.
            let trans = ( Floor (Val g1 / 360.) * 360. ).Eval ifl
            let g1t, g2t = ifl.minus( g1, trans), ifl.minus( g2, trans)
            if ifl.float g1t < 180. then
                // Cos is monotone decreasing on (0°,180°)
                if  ifl.float g2t < 180. || (g2t = ifl.OneHundredEighty && b2) then (cosdeg ifl g2t, cosdeg ifl g1t), (b2, b1)
                elif ifl.float g2t < 360. || (g2t = ifl.ThreeHundredSixty && b2) then
                    // Angle spans 180 degrees; break the tie for the high bound
                    if cosdeg ifl g1t < cosdeg ifl g2t then (ifl.MinusOne, cosdeg ifl g2t), (Closed, b2)
                    elif cosdeg ifl g1t > cosdeg ifl g2t then (ifl.MinusOne, cosdeg ifl g1t), (Closed, b1)
                    else (ifl.MinusOne, cosdeg ifl g1t), (Closed, b1 && b2)
                else (ifl.MinusOne, ifl.One), (Closed, Closed)
            // g1 is in interval [180°,360°):
            else
                // Cosine is monotone increasing on [180°,360°):
                if ifl.float g2t < 360. || (g2t = ifl.ThreeHundredSixty && b2) then (cosdeg ifl g1t, cosdeg ifl g2t), (b1, b2)
                // Angle spans 360 degrees; break the tie for the low bound
                else
                    if cosdeg ifl g1t > cosdeg ifl g2t then (cosdeg ifl g2t, ifl.One), (b2, Closed)
                    elif cosdeg ifl g1t < cosdeg ifl g2t then (cosdeg ifl g1t, ifl.One), (b1, Closed)
                    else (cosdeg ifl g1t, ifl.One), (b1 && b2, Closed)

    // Cosine in the u-layer, with tallying of bits and numbers moved.
    let cosu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let cosi = cosg env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env cosi;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, cosi
        ) ub

    // Sine in the g-layer.
    let sing (ifl : IFloat<_>) g = let (g1, g2), (b1, b2) = g in cosg ifl ((ifl.minuslfloat( 90., g2 ), ifl.minuslfloat( 90., g1)), (b2, b1))

    // Sine in the u-layer, with tallying of bits and numbers moved.
    let sinu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let sinu = sing env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env sinu;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, sinu
        ) ub

    let cotdeg (ifl : IFloat<_>) x = ( 1. / Tan ( Val x * Val ifl.Pi / 180. ) ).Eval ifl

    // Cotangent in the g-layer.
    let cotg (ifl : IFloat<_>) g =
        let (g1, g2), (b1, b2) = g
        if ifl.IsNaN g1 || ifl.IsNaN g2 then (ifl.NaN, ifl.NaN), (Open, Open)
        elif ifl.abs g1 = ifl.PosInf || ifl.abs g2 = ifl.PosInf then (ifl.NaN, ifl.NaN), (Open, Open)
        elif ifl.float( ifl.minus( g2, g1 ) ) > 180. then (ifl.NaN, ifl.NaN), (Open, Open)
        else
            // Translate g1 and g2 so g1 is in [0,180). This also assures that g2 is in [0,360], because of the previous If test.
            let trans = ( Floor (Val g1 / 180.) * 180. ).Eval ifl
            let g1t, g2t = ifl.minus( g1, trans), ifl.minus( g2, trans)
            if g1t = ifl.Zero && not b1 then (ifl.NaN, ifl.NaN), (Open, Open) // Cot[0°] is treated like 1/0
            elif g1t = ifl.Zero && b1 then
                if ifl.float g2t < 180. then (cotdeg ifl g2t, ifl.PosInf), (b2, Open)
                elif g2t = ifl.OneHundredEighty && b2 then (ifl.NegInf, ifl.NegInf), (Open, Open)
                else (ifl.NaN, ifl.NaN), (Open, Open)
            elif ifl.float g1t < 180. then
                if ifl.float g2t < 180. then (cotdeg ifl g2, cotdeg ifl g1), (b2, b1)
                elif g2t = ifl.OneHundredEighty && b2 then (ifl.NegInf, cotdeg ifl g1t), (Open, b1)
                else (ifl.NaN, ifl.NaN), (Open, Open)
            else (ifl.NaN, ifl.NaN), (Open, Open)

    // Cotangent in the u-layer, with tallying of bits and numbers moved. *)
    let cotu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let cota = cotg env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env cota;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, cota
        ) ub

    // Tangent in the g-layer.
    let tang (ifl : IFloat<_>) g = let (g1, g2), (b1, b2) = g in cotg ifl ((ifl.minuslfloat( 90., g2 ), ifl.minuslfloat( 90., g1 )), (b2, b1))

    // Tangent in the u-layer, with tallying of bits and numbers moved.
    let tanu env dmoved ub =
        ifUboundCompute env ( fun x -> 
        let tange = tang env.ifl (ubound2g_nc env x) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env tange;
                                            numbersmoved = dm.numbersmoved + 2 }
                        | None -> None
        datamoved, tange
        ) ub

    // Fused multiply-add in the g-layer.
    let fmag (ifl : IFloat<_>) ag bg cg = plusg ifl (timesg ifl ag bg) cg

    // Fused multiply - add in the u - layer, with tallying of bits and numbers moved.
    let fmagu env dmoved ub vb wb =
        if3UboundCompute env ( fun x y z -> 
        let ma = fmag env.ifl (ubound2g_nc env x) (ubound2g_nc env y) (ubound2g_nc env z) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env vb + nbits env wb + nbits env ma;
                                            numbersmoved = dm.numbersmoved + 4 }
                        | None -> None
        datamoved, ma
        ) ub vb wb

    // Fused dot product, entirely in the g-layer.
    let fdotg (ifl : IFloat<_>) agl bgl =
        if List.length agl <> List.length bgl then failwith <| sprintf "ERROR: in fdotg the lists have different length: %d and %d." (List.length agl) (List.length bgl)
        else
            List.map2 (fun ag bg -> timesg ifl ag bg) agl bgl |> List.reduce (fun acc ag -> plusg ifl acc ag)

    // Fused dot product in g-layer, with inputs and output in the u-layer and with tallying of bits moved and numbers moved.
    let fdotu env dmoved aul bul =
        let len = List.length aul
        if len <> List.length bul then failwith <| sprintf "ERROR: in fdotu the lists have different length: %d and %d." (List.length aul) (List.length bul)
        elif List.exists (fun au -> not <| uboundQ env au) aul || List.exists (fun bu -> not <| uboundQ env bu) bul then
            failwith "ERROR: in fdotu lists contain not ubound item."
        else 
            match dmoved with
            | Some(dm) ->
                let fdg, bits = List.map2 (fun au bu -> let tg = timesg env.ifl (ubound2g_nc env au) (ubound2g_nc env bu) in tg, (nbits env au + nbits env bu)) aul bul
                                |> List.reduce (fun (accg,accnb) (xg,xnb) -> plusg env.ifl accg xg, accnb + xnb )
                let fdu = g2u env fdg
                Some { ubitsmoved = dm.ubitsmoved + bits + nbits env fdu; numbersmoved = dm.numbersmoved + 2 * len + 1 }, fdu
            | None ->
                let fdu = List.map2 (fun au bu -> timesg env.ifl (ubound2g_nc env au) (ubound2g_nc env bu)) aul bul |> List.reduce (fun x y -> plusg env.ifl x y) |> g2u env
                None, fdu

    // Fused imaginary part of the product a + i b and c + i d in the g-layer: (ad + bc)
    let improdg (ifl : IFloat<_>) (ag, bg) (cg, dg) = fdotg ifl [ag;bg] [dg;cg]

    // Fused imaginary part product in the g-layer, with inputs and output in the u-layer and with tallying of bits moved and numbers moved.
    let improdu env dmoved (au, bu) (cu, du) = fdotu env dmoved [au;bu] [du;cu]

    // Fused real part of the product a + i b and c + i d in the g-layer (ac - bd)
    let realprodg (ifl : IFloat<_>) (ag, bg) (cg, dg) = fdotg ifl [ag;bg] [cg; negateg ifl dg]

    // Fused real part product in the g-layer, with inputs and output in the u-layer and with tallying of bits moved and numbers moved.
    let realprodu env dmoved (au, bu) (cu, du) = fdotu env dmoved [au;bu] [cu; negateu env du]

    // Fused sum of a list, entirely in the g - layer.
    let fsumg (ifl : IFloat<_>) agl = List.reduce (fun acc ag -> plusg ifl acc ag) agl

    // Fused sum of a list, with inputs and output in the u - layer and with tallying of bits and numbers moved.
    let fsumu env dmoved aul =
        let ifl = env.ifl
        if List.exists (fun au -> not <| uboundQ env au) aul then
            failwith "ERROR: in fsumu list contains not ubound item."
        else 
            match dmoved with
            | Some(dm) ->
                let fsg, bits = List.fold (fun (accg, accnb) au -> let tg = plusg ifl accg (ubound2g_nc env au) in tg, accnb + (nbits env au) ) (f2g ifl ifl.Zero, dm.ubitsmoved) aul
                let fsu = g2u env fsg
                Some { ubitsmoved = dm.ubitsmoved + bits + nbits env fsu; numbersmoved = dm.numbersmoved + List.length aul + 1 }, fsu
            | None ->
                let fsu = List.fold (fun acc au -> plusg ifl acc (ubound2g_nc env au) ) (f2g ifl ifl.Zero) aul |> g2u env
                None, fsu

    // Fused product of a list, entirely in the g - layer.
    let fprodg (ifl : IFloat<_>) agl = List.reduce (fun acc ag -> timesg ifl acc ag) agl

    // Fused product of a list, with inputs and output in the u - layer and with tallying of bits and numbers moved.
    let fprodu env dmoved aul =
        let ifl = env.ifl
        if List.exists (fun au -> not <| uboundQ env au) aul then
            failwith "ERROR: in fprodu list contains not ubound item."
        else 
            match dmoved with
            | Some(dm) ->
                let fpg, bits = List.fold (fun (accg, accnb) au -> let tg = timesg ifl accg (ubound2g_nc env au) in tg, accnb + (nbits env au) ) (f2g ifl ifl.Zero, dm.ubitsmoved) aul
                let fpu = g2u env fpg
                Some { ubitsmoved = dm.ubitsmoved + bits + nbits env fpu; numbersmoved = dm.numbersmoved + List.length aul + 1 }, fpu
            | None ->
                let fpu = List.fold (fun acc au -> timesg ifl acc (ubound2g env au) ) (f2g ifl ifl.Zero) aul |> g2u env
                None, fpu

    // Fused add - multiply in the g - layer.
    let famg (ifl : IFloat<_>) ag bg cg = timesg ifl (plusg ifl ag bg) cg

    // Fused add -  multiply in the u - layer, with tallying of bits and numbers moved.
    let famu env dmoved ub vb wb =
        if3UboundCompute env ( fun x y z -> 
        let am = famg env.ifl (ubound2g_nc env x) (ubound2g_nc env y) (ubound2g_nc env z) |> g2u env
        let datamoved = match dmoved with
                        | Some(dm) -> Some {ubitsmoved = dm.ubitsmoved + nbits env ub + nbits env vb + nbits env wb + nbits env am;
                                            numbersmoved = dm.numbersmoved + 4 }
                        | None -> None
        datamoved, am
        ) ub vb wb

    // Fused product ratio, entirely in the g - layer.
    let fprodratiog (ifl : IFloat<_>) numgl denomgl = divideg ifl (fprodg ifl numgl) (fprodg ifl denomgl)

    // Fused product ratio in the u - layer, with tallying of bits and numbers moved.
    let fprodratiou env dmoved numul denomul = 
        let ifl = env.ifl
        let len = List.length numul
        if List.exists (fun numu -> not <| uboundQ env numu) numul || List.exists (fun denomu -> not <| uboundQ env denomu) denomul then
            failwith "ERROR: in fprodratiou list contain not ubound item."
        else 
            match dmoved with
            | Some(dm) ->
                let pdeng, denbits = List.fold (fun (accg, accnb) denomu ->
                                     let tg = timesg ifl accg (ubound2g_nc env denomu) in tg, accnb + (nbits env denomu) ) (f2g ifl ifl.One, dm.ubitsmoved) denomul
                let pnumg, bits = List.fold (fun (accg, accnb) numu ->
                                  let tg = timesg ifl accg (ubound2g_nc env numu) in tg, accnb + (nbits env numu) ) (f2g ifl ifl.One, denbits) numul
                let divu = g2u env <| divideg ifl pnumg pdeng
                Some { ubitsmoved = bits + nbits env divu; numbersmoved = dm.numbersmoved + List.length numul + List.length denomul + 1 }, divu
            | None ->
                let pdeng = List.fold (fun acc denomu -> timesg ifl acc (ubound2g_nc env denomu)) (f2g ifl ifl.One) denomul
                let pnumg = List.fold (fun acc numu -> timesg ifl acc (ubound2g_nc env numu)) (f2g ifl ifl.One) numul
                None, g2u env <| divideg ifl pnumg pdeng

    let choose n k = List.fold (fun acc i -> acc * (n - i + 1) / i) 1 [1..k]

    // Polynomial helper function that uses powers of x - x0 instead of x.
    let polyTg (ifl : IFloat<'F>) (coeffsg: (('F*'F)*(bool*bool)) list) xg x0g =
        let k = coeffsg.Length
        let (x0lo, x0hi), _ = x0g
        if x0lo = ifl.NegInf || x0hi = ifl.PosInf then (ifl.NegInf, ifl.PosInf), (Closed, Closed)
        else
            let coeffsg1 =
                List.mapi
                    (fun j c ->
                    let bi = choose (k-1) j
                    let pg_ = timesg ifl coeffsg.[k - 1] ((ifl.from (float bi), ifl.from (float bi)),(Closed, Closed))
                    let _, pg1 = fWhile (fun (i, _) -> i >= j)
                                    ( fun (i, pg) ->
                                    let bi_ = choose i j
                                    let pg' = plusg ifl ( timesg ifl coeffsg.[i] ((ifl.from( float bi_ ),ifl.from( float bi_ )),(Closed, Closed)) ) (timesg ifl x0g pg)
                                    i - 1, pg'
                                    ) (k - 2, pg_)
                    pg1
                    ) coeffsg
            let k1 = coeffsg1.Length
            let xmg = minusg ifl xg x0g
            let pg2 = coeffsg1.[k1 - 1]
            let _, pg3 = fWhile (fun (i, _) -> i >= 1)
                             ( fun (i, pg) ->
                             i - 1, plusg ifl (timesg ifl pg xmg) coeffsg1.[i-1]
                             ) (k1 - 1, pg2)
            pg3

    // Polynomial helper function that evaluates a polynomial at the endpoints
    // of an inexact unum, and intersects them to tighten the result.
    let polyinexactg (ifl : IFloat<'F>) coeffsg xg =
        let (xlo, xhi), _ = xg
        intersectg ifl ( polyTg ifl coeffsg xg ((xlo, xlo),(Closed, Closed)) )
                       ( polyTg ifl coeffsg xg ((xhi, xhi),(Closed, Closed)) )

    // Polynomial evaluation of an exact general interval using Horner's rule
    let polyexactg (ifl : IFloat<'F>) (coeffsg: _ list) xg =
        let k = coeffsg.Length
        let pg = List.last coeffsg
        let _, pg1 = fWhile (fun (i, pg_) -> i >= 0)
                        ( fun (i, pg_) ->
                            i - 1, plusg ifl coeffsg.[i] (timesg ifl pg_ xg)
                        ) (k - 2, pg)
        pg1

    // Bisect an inexact general interval along a coarsest-possible ULP boundary.
    let bisect env g_ =
        let ifl = env.ifl
        ifGCompute ifl (
            fun g ->
                let (gL, gR), (gLb, gRb) = g
                let gM = if gL < ifl.Zero && gR > ifl.Zero then ifl.Zero
                         elif gL = ifl.NegInf && gR > ifl.from -env.maxreal then ifl.from -env.maxreal
                         elif gL < ifl.from env.maxreal && gR = ifl.PosInf then ifl.from env.maxreal
                         else
                            let m = ( From 2. ** Floor ( Log2 (Val gR - Val gL) ) ).Eval ifl
                            if IsInteger ifl ( (Val gL / Val m).Eval ifl) then
                                if ((Val gR - Val gL).Eval ifl) = m then ( (Val gL + Val gR) / 2. ).Eval ifl
                                else ( Val m * Floor (Val gL / Val m + 1.) ).Eval ifl
                            else ( Val m * Ceil (Val gL / Val m) ).Eval ifl
                // should be a list instead of a tuple ?
                [ (gL, gM), (gLb, Open); (gM, gR), (Open, gRb) ]
        ) g_

    let glistQ (ifl : IFloat<'F>) gl = not <| List.exists (fun x -> not <| gQ ifl x) gl

    let glistNaNQ (ifl : IFloat<'F>) gl = List.exists (fun x -> let (xL, xR), _ = x in ifl.IsNaN xL || ifl.IsNaN xR) gl

    // Polynomial evaluation of a general interval without u-layer information loss.
    let polyg env coeffsg xg =
        let ifl = env.ifl
        if glistQ ifl coeffsg && gQ ifl xg then
            let k = coeffsg.Length
            let (xgL, xgR), (xgLb, xgRb) = xg
            if ifl.IsNaN xgL || ifl.IsNaN  xgR || glistNaNQ ifl coeffsg then (ifl.NaN, ifl.NaN), (Open, Open)
            // Constant case. Just return the first (and only coefficient).
            elif k = 1 then List.head coeffsg
            // Linear case is a fused multiply-add; no dependency problem.
            elif k = 2 then fmag ifl coeffsg.[1] xg (List.head coeffsg)
            // Exact argument is also easy, since no dependency problem.
            elif xgL = xgR then polyexactg ifl coeffsg xg
            // Quadratic or higher requires finesse. Intersect the two endpoint-based evaluations.
            else
                let gL = polyexactg ifl coeffsg ((xgL,xgL),(Closed,Closed))
                let gL1 = if xgLb then (fst gL),(Open,Open) else gL
                let gR = polyexactg ifl coeffsg ((xgR,xgR),(Closed,Closed))
                let gR1 = if xgRb then (fst gR),(Open,Open) else gR
                let (gLL,gLR),(gLLb,gLRb) = gL1
                let (gRL,gRR),(gRLb,gRRb) = gR1
                let minLSide = gLL < gRL || (gLL = gRL && not gLLb)
                let min_, minQ = if minLSide then gLL, gLLb else gRL, gRLb
                let maxLSide = gLR > gRR || (gLR = gRR && not gLRb)
                let max_, maxQ = if maxLSide then gLR, gLRb else gRR, gRRb
                let trials_ = [xg]
                let M_ = ((min_,max_),(minQ,maxQ))
                let M1, _ = fWhile ( fun (_, (trials:_ list)) -> trials.Length >= 1 )
                                ( fun (M, trials) ->
                                let pg = polyinexactg ifl coeffsg (List.head trials)
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
                                    let (_, tr0R), _ = List.head trials1
                                    let gM = polyexactg ifl coeffsg ((tr0R,tr0R),(Closed,Closed))
                                    let (gML, gMR), (gMLb, gMRb) = gM
                                    let (mint_,maxt_),(mintQ,maxtQ) = M1
                                    let mint1, mint1Q = if gML < mint_ || (gML = mint_ && not gMLb) then gML, gMLb else mint_, mintQ
                                    let maxt1, maxt1Q = if gMR > maxt_ || (gMR = maxt_ && not gMRb) then gMR, gMRb else maxt_, maxtQ
                                    ((mint1,maxt1),(mint1Q,maxt1Q)), trials1
                                ) (M_, trials_)
                M1
        else (ifl.NaN, ifl.NaN), (Open, Open)

    let polyu env coeffsu_ u_ =
        ifUboundListCompute env (fun coeffsu ->
             ifUboundCompute env (fun u ->
             let coeffsg = [for u in coeffsu do yield ubound2g env u]
             g2u env ( polyg env coeffsg (ubound2g env u) )
             ) u_
        ) coeffsu_

    // Unify if information-per-bit improves by at least "ratio".
    let smartunify env ub ratio =
        let ifl = env.ifl
        let (glo, ghi),_ = ubound2g_nc env ub
        let v = unify env ub
        let (vlo, vhi),_ = ubound2g_nc env v
        let widthbefore = ifl.float( ifl.minus( ghi, glo ) )
        let widthafter = ifl.float( ifl.minus( vhi, vlo ) )
        let nbitsbefore = float <| nbits env ub
        let nbitsafter = float <| nbits env v
        if widthafter = Double.PositiveInfinity then if ratio >= 1. then v else ub
        elif widthafter = 0. then v
        elif (widthbefore/widthafter) * (nbitsbefore/nbitsafter) >= ratio then v
        else ub
  
    // Complex Fast Fourier Transform using unum arithmetic. *)
    let cfftu env (rru : (ubound*ubound) []) n iflg =
        let ifl = env.ifl
        let ggu = Array.copy rru
        let k_ = n / 2
        let th = if iflg >= 0 then ifl.negate ifl.Pi else ifl.Pi
        let dmoved_ = {numbersmoved = 0; ubitsmoved = 0}
        let _, dmovednew =
               fWhile  ( fun (k, dmoved) -> k >= 1 )
                       ( fun (k, dmoved) ->
                                let mutable dm_ = dmoved
                                let wwu = Unum(x2u env <| ( From -2. * ( Sin ( Val th / ( 2. * float k ) ) ) ** From 2. ).Eval ifl) , Unum( x2u env <| (Sin (Val th / float k)).Eval ifl )
                                let mutable twiddleu = Unum(env.oneu), Unum(env.zerou)
                                for j in [0..k - 1] do
                                    for i in [1..2*k..n] do
                                        // t = g[i+j] - g[i+j+k]
                                        let dm1, tru_ = minusu env dm_ (fst (ggu.[i+j])) (fst ggu.[i+j+k]) // Re
                                        let tru = smartunify env tru_ 1.
                                        let dm2, tiu_ = minusu env dm1 (snd ggu.[i+j]) (snd ggu.[i+j+k]) // Im
                                        let tiu = smartunify env tiu_ 1.
                                        // g[i+j] = g[i+j] + g[i+j+k]
                                        let dm3, ggu_r_ij_ = plusu env dm2 (fst (ggu.[i+j])) (fst ggu.[i+j+k])
                                        let ggu_r_ij = smartunify env ggu_r_ij_ 1.
                                        let dm4, ggu_i_ij_ = plusu env dm3 (snd (ggu.[i+j])) (snd ggu.[i+j+k])
                                        let ggu_i_ij = smartunify env ggu_i_ij_ 1.
                                        ggu.[i+j] <- ggu_r_ij, ggu_i_ij
                                        // g[i+j+k] = twiddle * (g[i+j] - g[i+j+k]) = twiddle * t
                                        let dm5, ggu_r_ijk_ = realprodu env dm4 twiddleu (tru, tiu)
                                        let ggu_r_ijk = smartunify env ggu_r_ijk_ 1.
                                        let dm6, ggu_i_ijk_ = improdu env dm5 twiddleu (tru, tiu)
                                        let ggu_i_ijk = smartunify env ggu_i_ijk_ 1.
                                        ggu.[i+j+k] <- ggu_r_ijk, ggu_i_ijk
                                        dm_ <- dm6
                                    // twiddle = twiddle * ww + twiddle
                                    let dmj1, twr_ = realprodu env dm_ twiddleu wwu
                                    let dmj2, twr = plusu env dmj1 twr_ (fst twiddleu)
                                    let dmj3, twi_ = improdu env dm_ twiddleu wwu
                                    let dmj4, twi = plusu env dmj1 twi_ (snd twiddleu)
                                    twiddleu <- twr, twi
                                    dm_ <- dmj4
                                k / 2, dm_ )
                       (k_, Some(dmoved_))
        let mutable j = 0
        for i in [0..n-2] do
            if i < j then
                let t = ggu.[j+1]
                ggu.[j+1] <- ggu.[i+1]
                ggu.[i+1] <- t
            else ()
            let mutable k = n / 2
            while k <= j do
                j <- j - k
                k <- k / 2
            j <- j + k
        dmovednew, ggu

    // Find the width of the ULP to the right of an exact unum
    let ulphi env u_ =
        ifExactUnumCompute env (fun u ->
        let v = if ltuQ env (Unum(u)) (Unum(env.zerou)) then u - env.ubitmask else u + env.ubitmask
        let (glo, ghi),_ = unum2g_nc env v in env.ifl.minus(ghi, glo)
        ) u_

    // Look for alternative unum string that favors the exponent.
    let favore env u_ =
        ifUnumCompute env (fun u ->
        let ut = demotef env <| promotee env u
        if inexQ_nc env ut || esize_nc env ut = uint64 env.espmax || fsize_nc env ut = 1UL then ut
        else fWhile (fun v -> fsize_nc env v > 1UL && exQ_nc env (demotef env v)) (demotef env) ut
        ) u_

    // Pad the fraction out to its maximum size by shifting in zero bits. \
    let padu env u_ =
        ifUnumCompute env (fun u ->
        let fs = fsize_nc env u
        (( (floatmask_nc env u) &&& u ) <<< (env.fspmax - int fs ))
        + (env.utagmask &&& u) + uint64 env.fspmax - fs
        ) u_

    // Look for alternative unum string that favors the fraction.
    let favorf env u_ =
        ifUnumCompute env ( fun u ->
        let ut = demotee env <| padu env u
        if inexQ_nc env ut then ut else
            let ut1, _ =
                fWhile
                    (fun (ut_, utf) -> fsize_nc env ut_ > 1UL && exQ_nc env <| utf)
                    (fun (ut_, utf) -> utf, demotef env ut_)
                    (ut, demotef env ut)
            ut1
        ) u_

    // Find the right neighbor of a unum
    let nborhi env u_ minpower =
        ifUnumCompute env ( fun u ->
        let ifl = env.ifl
        let ut = if u = ((env.utagmask + signmask_nc env u) &&& u) && exQ_nc env u then env.zerou else u
        let s = int <| -1. ** float (sign_nc env ut)
        let overflow, ulpminu = 
            if minpower < log2 env.smallsubnormal then false, env.smallsubnormalu
            elif minpower > log2 env.maxreal then true, x2u env <| ifl.from (2.**floor(log2 env.maxreal))
            else false, x2u env <| ifl.from (2.**minpower)
        let ulpmin = leftFloat <| unum2g_nc env ulpminu
        if u = env.posinfu || u = env.sNaNu || u = env.qNaNu then env.qNaNu // Values without nbors on the high side
        elif u = env.neginfu then 
            if overflow then 
                if env.utagmask = 1UL then (x2u env (ifl.from -2.)) + env.ubitmask // Warlpiri environment
                else (x2u env (ifl.from -3.)) + env.ubitmask
            else env.negbigu + env.ubitmask // If -Inf, use the (-Inf, x) unum with the most neg. x, unless the requested minpower caused overflow.
        elif inexQ_nc env u then x2u env ( rightFloat (unum2g_nc env u) ) // If inexact, always use the exact upper value
        elif overflow && u = env.twou && env.utagmask = 1UL then env.twou + env.ubitmask // Warlpiri "many"
        elif overflow && u = env.threeu && env.utagmask <> 1UL then env.threeu + env.ubitmask // Also OK to use (3, +Inf)
        // OK to overflow to +Inf if the minpower overflowed the environment.
        else // Reduce ULP until it equals ulpmin, or we run out of exponent and fraction bits
            let t = leftFloat <| unum2g_nc env ut
            let ut0 = x2u env t 
            let ulpmin1 = fWhile ( fun ulpm -> not (IsInteger ifl (ifl.divides(t, ulpm))) ) (fun ulpm -> ifl.dividesrfloat(ulpm, 2.)) ulpmin
            let ut1, _ =
                fWhile
                    (fun (ut_, utf) -> ulphi env ut_ < ulpmin1 && ut_ <> utf)
                    (fun (ut_, utf) -> utf, favorf env utf)
                    (ut0, favorf env ut0)
            let ut2, _ =
                fWhile
                    (fun (ut_, ute) -> esize_nc env ut_ < uint64 env.espmax && ulphi env ute >= ulpmin1)
                    (fun (ut_, ute) -> ute, promotee env ute)
                    (ut1, promotee env ut1)
            let ut3, _ =
                fWhile
                    (fun (ut_, utf) -> fsize_nc env ut_ < uint64 env.fspmax && ulphi env utf >= ulpmin1)
                    (fun (ut_, utf) -> utf, promotef env utf)
                    (ut2, promotef env ut2)
            if s = 1 then ut3 + env.ubitmask else ut3 - env.ubitmask
        ) u_

    // Find the left neighbor of a unum
    let nborlo env u_ minpower =
        ifUnumCompute env ( fun u ->
        // Watch out for negative zero, otherwise use nborhi
        if sameuQ env (Unum u) (Unum (env.zerou)) && minpower < log2 env.smallsubnormal then
            env.smallsubnormalu + env.signbigu - env.ubitmask
        else
            let nu = fstBound <| negateu env (Unum u)
            let nhi = nborhi env nu minpower
            fstBound <| negateu env (Unum nhi)
        ) u_

    // Create a list of 1-dimensional uboxes from a ubound.
    let uboxlist env ub_ minpower =
        ifUboundCompute env (fun ub ->
        let u1 = fstBound ub
        let u2 = sndBound ub
        let utest = if u1 = env.neginfu then env.neginfu else nborhi env (nborlo env u1 minpower) minpower
        if u1 = env.qNaNu || u2 = env.qNaNu || u1 = env.sNaNu || u2 = env.sNaNu then [env.qNaNu]
        elif sameuQ env ub (Unum(env.neginfu)) then [env.neginfu]
        elif sameuQ env ub (Unum(env.posinfu)) then [env.posinfu]
        // Go up until we exceed the ubound range.  Possible to exceed using first utest!
        else
            let infinitybits = env.ubitmask + expomask env utest + fracmask env utest
            let nbortemp = nborhi env utest minpower
            let utest1 = if infinitybits &&& utest = infinitybits && esize env utest < uint64 env.espmax
                            && nequQ env (intersectu env ub (Unum nbortemp)) (Unum nbortemp) then
                            promotee env (exact env utest) + if inexQ env utest then env.ubitmask else 0UL
                         else utest
            let _, list1_ = fWhile
                                     (fun (ut, l1) ->
                                     let ints = (intersectu env ub (Unum ut))
                                     sameuQ env ints (Unum ut) && ut <> env.posinfu)
                                     (fun (ut, l1) ->
                                        let l1_ = ut :: l1
                                        let ut_ = nborhi env ut minpower 
                                        let ut1 = if infinitybits &&& ut_ = infinitybits && esize env ut_ < uint64 env.espmax 
                                                     && nequQ env (intersectu env ub (Unum ut_)) (Unum ut_) then
                                                    promotee env (exact env ut_) + if inexQ env utest then env.ubitmask else 0UL
                                                  else ut_
                                        ut1, l1_
                                     ) (utest1, [])
            // Start from other end and go down until utest equals last element of list1.
            let utest3 = if u2 = env.posinfu then env.posinfu else nborlo env (nborhi env u2 minpower) minpower
            // note: list1_ is in reverse order so List.head is actually the last element produced
            let _, list2 = fWhile ( fun (ut, _) -> (gtuQ env (Unum ut) (if list1_.Length = 0 then Unum u1 else Unum (List.head list1_)) && ut <> env.neginfu) )
                                  ( fun (ut, l2) -> nborlo env ut minpower, ut :: l2 ) (utest3, [])
            // this reverses list1_ and prepend it in front of list2, finally producing: list1 @ list2 but efficiently, without copying the whole data at each step.
            List.fold (fun acc ut -> ut :: acc) list2 list1_
        ) ub_

    // Create a 1-dimensional ubox list that leaves out the exact unums.
    let uboxlistinexact env ub_ minpower = 
        ifUboundCompute env ( fun ub ->
        let set_ = uboxlist env ub minpower
        List.rev <| List.fold ( fun acc ut -> if inexQ env ut then ut :: acc else acc ) [] set_
        ) ub_

    // Split a ubound into three parts, if possible.
    let splitub env ub_ =
        ifUboundCompute env ( fun ub ->
            let ifl = env.ifl
            let (g1, g2), (b1, b2) = ubound2g_nc env ub
            if ifl.IsNaN g1 &&  ifl.IsNaN g2 && b1 && b2 then [ub]
            elif not b1 && not b2 then
                if g1 = g2 then [ub] // Cannot split exact single values
                else [ (Unum(fstBound ub)); g2u env ((g1, g2), (Open, Open)); Unum (sndBound ub) ] // else cleave off exact endpoints
            elif b1 && not b2 then [ g2u env ((g1, g2), (Open, Open)); Unum (sndBound ub) ] // cleave off exact right endpoint
            elif not b1 && b2 then [ Unum (fstBound ub); g2u env ((g1, g2), (Open, Open)) ] // cleave off exact left endpoint
            elif g1 = ifl.NegInf then
                if g2 = ifl.from -env.maxreal then [ub] // Cannot split the negative "many" region
                else [(Unum(env.negbigu + env.ubitmask)); (Unum(env.negbigu)); g2u env ( (ifl.from -env.maxreal, g2), (Open, Open) ) ]
            elif g2 = ifl.NegInf then
                if g1 = ifl.from env.maxreal then [ub] // Cannot split the positive "many" region
                else [ g2u env ( (g1, ifl.from env.maxreal), (Open, Open) ); Unum (env.maxrealu); Unum (env.maxrealu + env.ubitmask) ]
            else
                // See if open interval contains a unum different from either endpoint:
                let (gm1, gm2), _ = unum2g_nc env ( x2u env ((( (Val g1 + Val g2) / 2. ) ).Eval ifl) )
                if gm1 > g1 then [ g2u env ((g1, gm1), (Open, Open)); Unum (x2u env gm1); g2u env ((gm1, g2), (Open, Open))]
                elif gm2 < g2 then [ g2u env ((g1, gm2), (Open, Open)); Unum (x2u env gm2); g2u env ((gm2, g2), (Open, Open))]
                else [ub] //Cannot split; must be the samllest ULP size.
        ) ub_

    let replaceat (a: 'a list) k v = [ for x in a.[..k - 1] do yield x ; yield v; for x in a.[k + 1..] do yield x ]

    let IsUnum = function | Unum _ -> true | _ -> false 

    // Make a single pass at a set of 2-dimensional uboxes to
    // coalesce subsets that form a coarser single ULP-wide unum.
    let coalescepass env set =
        let ifl = env.ifl
        let ndim = List.length <| List.head set // each sub-set has a fixed dimension ndim
        // make a g-layer list of list from the ubound ones
        let gset_ = [ for l in set do yield [ for ub in l do yield ubound2g env ub] ]
        let j_ = 0
        let _, gsetnj =
            fWhile (fun (j, gsetj) -> j < ndim)
                (fun (j, gsetj) ->
                let i_ = 0
                let _, gsetnj =
                    fWhile (fun (i, (gset : (('F*'F)*(bool*bool)) list list )) -> i < gset.Length)
                        (fun (i, gset) ->
                        let g = gset.[i]
                        let (gjlo, gjhi), (gjlob, gjhib) = g.[j]
                        if (gjlob, gjhib) = (Open, Open) then
                            let width = ifl.minus( gjhi, gjlo )
                            if ifl.float gjlo >= 0. then
                                let gset1 = if EvenQ ifl (ifl.divides( gjlo, width )) && IsUnum ( g2u env ((ifl.minus(gjhi, width), ifl.plus(gjhi, width)),(Open, Open)) ) then
                                                let g1 = replaceat g j ((gjhi, gjhi), (Closed, Closed))
                                                let g2 = replaceat g j ((ifl.plus(gjlo, width), ifl.plus(gjhi, width)), (Open, Open))
                                                let i1 = try List.findIndex (fun gt -> gt = g1) gset with | _ -> -1
                                                let i2 = try List.findIndex (fun gt -> gt = g2) gset with | _ -> -1
                                                if i1 <> -1 && i2 <> -1 then
                                                    List.sort <| List.distinct
                                                        [ for k in [0..gset.Length - 1] do if k <> j && k <> i1 && k <> i2 then yield gset.[k]
                                                          yield replaceat g j ((gjlo, ifl.plus(gjhi, width)), (Open, Open)) ]
                                                else gset
                                             elif EvenQ ifl (ifl.divides(gjhi, width)) && IsUnum ( g2u env ((ifl.minus(gjlo, width), ifl.plus(gjlo, width)),(Open, Open)) ) then
                                                let g1 = replaceat g j ((gjlo, gjlo), (Closed, Closed))
                                                let g2 = replaceat g j ((ifl.minus(gjlo, width), ifl.minus(gjhi, width)), (Open, Open))
                                                let i1 = try List.findIndex (fun gt -> gt = g1) gset with | _ -> -1
                                                let i2 = try List.findIndex (fun gt -> gt = g2) gset with | _ -> -1
                                                if i1 <> -1 && i2 <> -1 then
                                                    List.sort <| List.distinct
                                                        [ for k in [0..gset.Length - 1] do if k <> j && k <> i1 && k <> i2 then yield gset.[k]
                                                          yield replaceat g j ((ifl.minus(gjlo, width), gjhi), (Open, Open)) ]
                                                else gset
                                            else gset
                                i + 1, gset1
                            else i + 1, gset
                        else i + 1, gset
                        ) (i_, gsetj)
                j + 1, gsetnj
                ) (j_, gset_)
        [ for l in gsetnj do yield [ for g in l do yield g2u env g] ]

    // Make multiple passes at a set of 2 - dimensional uboxes to coalesce subsets
    // that form a coarser single ULP - wide unum, until all possible coalescing is done.
    let coalesce env set_ =
        let newset_ = coalescepass env set_
        let ns, _ = fWhile (fun (news, olds) -> news <> olds) (fun (news,olds) -> coalescepass env news, news) (newset_, set_)
        ns

    // Find the minimum of two endpoints, considering open-closed state.
    let minub env xub_ yub_ =
        if2UboundCompute env (fun xub yub ->
        let (xlo,xhi),(xlob,xhib) = ubound2g_nc env xub
        let (ylo,yhi),(ylob,yhib) = ubound2g_nc env yub
        if xlo < ylo || (xlo = ylo && not xlob) then xub else yub
        ) xub_ yub_

    // Find the maximum of two endpoints, considering open-closed state.
    let maxub env xub_ yub_ =
        if2UboundCompute env (fun xub yub ->
        let (xlo,xhi),(xlob,xhib) = ubound2g_nc env xub
        let (ylo,yhi),(ylob,yhib) = ubound2g_nc env yub
        if xhi > yhi || (xhi = yhi && not xhib) then xub else yub
        ) xub_ yub_

    // Add a ubound or unum to a 1-dimensional set of ubounds, coalescing if possible.
    let coalesce1D env ubset ub_ =
        ifUboundCompute env (fun ub ->
        let ifl = env.ifl
        if List.isEmpty ubset then [ ub ]
        else
            // First look for any overlapping or touching ubounds, and merge them with ut. If disjoint, append to newset.
            let _, ut1, newset1 = fWhile (fun (i, ut, newset) -> i < ubset.Length)
                                    (fun (i, ut, newset) ->
                                        let ut_, ns = if nnequQ env ubset.[i] ut
                                                         || nnequQ env (Unum (nborlo env (fstBound ubset.[i]) Double.NegativeInfinity)) ut
                                                         || nnequQ env (Unum (nborhi env (sndBound ubset.[i]) Double.NegativeInfinity)) ut then
                                                        let ut1_ = Bounds( fstBound (minub env ubset.[i] ut), sndBound (maxub env ubset.[i] ut) )
                                                        ut1_, newset
                                                      else ut, newset @ [ut]

                                        i + 1, ut_, ns
                                    )
                                    (0, ub, [])
            newset1 @ [ut1]
        ) ub_


    // Find the real-valued bounds of a 2-dimensional ubox.
    let boxbound2D env xub_ minpowerx yub_ minpowery =
        if2UboundCompute env (fun xub yub ->
        let ylist = uboxlist env yub minpowery
        let left = [ for i in [0..ylist.Length] do yield Bounds (fstBound xub, ylist.[i]) ]
        let right = [ for i in [0..ylist.Length] do yield Bounds (sndBound xub, ylist.[i]) ]
        let bottom = [ for i in [0..ylist.Length] do yield Bounds (ylist.[i], fstBound yub) ]
        let top = [ for i in [0..ylist.Length] do yield Bounds (ylist.[i], sndBound yub)  ]
        List.sort <| List.distinct ( List.concat [left; right; bottom; top] )
        ) xub_ yub_

    let drop (l: _ list) which = [ yield! l.[..fst which] ; yield! l.[snd which..] ]

    // The ubinsert insertion routine assumes ubset is a sorted set of disjoint ubounds, and has no NaN ubounds.
    let ubinsert env (ubset: _ list) ub_ =
        ifUboundCompute env ( fun ub ->
        let ifl = env.ifl
        let k = ubset.Length
        if k = 0 then [ub]
        else
            let j = fWhile (fun j_ -> j_ >= 0 && gtuQ env ubset.[j_ - 1] ub) (fun j_ -> j_ - 1) (k - 1)
            let lefttouch = if j >= 0 then nnequQ env (Unum (nborhi env (sndBound ubset.[j - 1]) Double.NegativeInfinity)) ub else false
            let righttouch = if j < k - 1 then nnequQ env (Unum (nborlo env (fstBound ubset.[j]) Double.NegativeInfinity)) ub else false
            // Joined on both sides.
            if lefttouch && righttouch then [ yield! drop ubset (j - 1, k - 1)
                                              yield Unum (fstBound ubset.[j - 1]); yield Unum (sndBound ubset.[j])
                                              yield! drop ubset (0, j)]
            // Joined on left side.
            elif lefttouch && not righttouch then
                                            [ yield! drop ubset (j - 1, k - 1)
                                              // ERROR unum.py j-1
                                              yield Unum (fstBound ubset.[j - 1]); yield Unum (sndBound ub)
                                              yield! drop ubset (0, j - 1)]
            // Joined on right side.
            elif not lefttouch && righttouch then
                                            [ yield! drop ubset (j, k - 1)
                                              yield Unum (sndBound ub); yield Unum (sndBound ubset.[j])
                                              yield! drop ubset (0, j)]
            // Inserted new ubound, not touching.
            else
               [ if j > k - 1 then yield! ubset else yield! drop ubset (j, k - 1); yield ub; yield! drop ubset (0, j - 1) ]
        ) ub_

    // The try-everything solver.
    let solveforub env domain condition =
        let _, sols =
            fWhile ( fun ((trials: _ list), sols_) -> trials.Length > 0 )
                ( fun (trials, sols_) -> 
                    List.fold ( fun (trials_, solst) ub ->
                                if condition ub then
                                    let temp = splitub env ub
                                    if temp.Length = 1 then
                                        // unsplittable. Join to the existing region or start new one.
                                        trials_, ubinsert env solst (List.head temp)
                                    else (List.sort <| temp @ trials_), solst
                                else trials_, solst
                                ) ([], sols_) trials
                ) (domain, [])
        sols

    // Tuples helper function for 2 lists
    let tuplesFrom2 l1 l2 =
        let lm = List.map ( fun i1 -> List.map (fun i2 -> (i1, i2) ) l2 ) l1
        let lflatten = List.foldBack (fun t acc -> List.foldBack (fun i ac -> i :: ac) t acc) lm []
        lflatten

    // mathematica tuples function
    let tuples (ll:_ list list) =
        let n = List.length ll
        let indexes = Array.zeroCreate n
        let lengths = [ for li in ll -> List.length li]
        let tot = List.reduce (*) lengths
        let rec incrementIndexes =
            function | -1 -> () // we're done 
                     | l -> if indexes.[l] = lengths.[l] - 1 then
                                indexes.[l] <- 0
                                incrementIndexes (l - 1)
                            else indexes.[l] <- indexes.[l] + 1
        let acc_, _ = fWhile (fun (acc, k) -> k < tot)
                        (fun (acc, k) ->
                            let newacc = [ for i in [0..n - 1] do yield ll.[i].[indexes.[i]] ]  :: acc
                            incrementIndexes  (n - 1)
                            newacc, k + 1
                        ) ([], 0)
        List.rev acc_

    // mathematica complement
    let complement toScan toExclude =
        let rec findInAny k ll_ =
            match ll_ with
            | [] -> []
            | ll -> let h = List.head ll
                    if List.exists (fun x -> x = k) h then h
                    else findInAny k (List.tail ll)
        let existsInAny k l = if findInAny k l = [] then false else true
        [ for i in toScan do if not (existsInAny i toExclude) then yield i ]

    // Find the neighbors, in all dimensions, of a unum.
    let findnbors env (set: uint64 list list) (minpowers: _ list) =
        let _, tempset = 
            fWhile (fun (i, tempset) -> i < set.Length)
                (fun (i, tempset) ->
                    let seti : _ list = set.[i]
                    let newt = [ for ts in tempset do yield ts;
                                 yield! tuples [ for j in [0..seti.Length] do yield [ nborlo env seti.[j] minpowers.[j] ; seti.[j] ; nborhi env seti.[j] minpowers.[j] ] ]
                               ]
                    i + 1, List.sort <| List.distinct newt
                ) (0, [])
        complement tempset [ set ]

    // Find the real value of the width of a unum or ubound.
    let widthu env ub_ =
        ifUboundCompute env (fun ub ->
            let (glo, ghi), _ = ubound2g_nc env ub in env.ifl.minus(ghi, glo)
        ) ub_

    // Find the total n - dimensional volume of a ubox set.
    let volume env set =
        let ifl = env.ifl
        List.reduce (fun x y -> ifl.plus(x, y)) <| List.map (fun s -> List.fold (fun prod ub -> ifl.times(prod, (widthu env ub))) ifl.One s ) set

    // Create a set of uboxes describing the rectangular bound around a given ubox.
    let spacestepbounds env ubox r =
        let ifl = env.ifl
        let ru = Unum <| x2u env r
        [| for ub in ubox do
                let sub = minusu env None ub ru
                yield Unum ( x2u env <| ifl.plusrfloat( leftFloat (ubound2g_nc env (snd sub)), env.smallsubnormal / 2. ) )
                let sum = plusu env None ub ru
                yield Unum ( x2u env <| ifl.minusrfloat( leftFloat (ubound2g_nc env (snd sum)), env.smallsubnormal / 2. ) ) |]

    // Create the set of all uboxes inside a bound.
    let spacestep env ubox r minpower =
        let bounds  = spacestepbounds env ubox r
        [| for ub in bounds do
            let ubl = uboxlist env ub minpower
            yield List.head ubl; yield List.last ubl |]

    // Check a ubound for intersection with a set of other ubounds.
    let setintersectQ env ubl set =
        List.exists (fun sl -> List.exists2 (fun s ub -> not <| nnequQ env s ub) sl ubl) set

    // Check a general interval for intersection with a set of other general intervals.
    let gsetintersectQ (ifl : IFloat<_>) gs gset =
         List.exists (fun gsetl -> List.exists2 (fun gsetg gsg -> not <| nneqgQ ifl gsetg gsg) gsetl gs) gset

    // Remove interior points from a set of uboxes, leaving the boundary only.
    let  hollowout env set =
        let n = List.length set
        let ndim = List.length ( List.head set )
        // set is set.length x ndim
        let gset = [ for sl in set do yield [ for s in sl do yield unum2g env s] ]
        let _, boundary = fWhile (fun (i, bound) -> i < n )
                            (fun (i, bound) ->
                                let ubi = set.[i]
                                let nbors = findnbors env [ ubi ] ( List.init ndim (fun x -> 0.) )
                                let nnbors = nbors.Length
                                let gnbors = [ for nbl in nbors do yield [ for nb in nbl do yield ubound2g env (Unum nb)] ]
                                let j = fWhile (fun j  -> j < nnbors && gsetintersectQ env.ifl gnbors.[j] gset) (fun j -> j + 1 ) 0
                                i + 1, if j < nnbors then ubi @ bound else bound
                            ) (0, [])
        boundary

    
    // Acceleration bound that avoids the dependency problem between numerator and denominator.
    let accub env xub yub =
        let ifl = env.ifl
        let amin = ifl.PosInf
        let amax = ifl.NegInf
        let bmin = ifl.PosInf
        let bmax = ifl.NegInf
        let (xlo, xhi), _ = ubound2g_nc env xub
        let (ylo, yhi), _ = ubound2g_nc env yub
        let tests = tuples [[xlo; xhi]; [ylo;yhi]]
        let updatedtests =
            List.fold (fun acc xi -> 
                List.fold (fun acc1 yj ->
                        List.fold (fun acc2 s ->
                            let Sqrt2 = Sqrt (From 2.)
                            let t1 =  ( Val s * Val yj / Sqrt2 ).Eval ifl
                            let acc3 = if xlo < t1 && t1 < xhi then acc2 @ [ [ t1; yj ] ] else acc2
                            let t2 =  ( Val s * Val xi / sqrt 2. ).Eval ifl
                            let acc4 = if ylo < t2 && t2 < yhi then acc3 @ [ [ xi; t2 ] ] else acc3
                            let t3 =  ( Val s * Val yj * Sqrt2 ).Eval ifl
                            let acc5 = if xlo < t3 && t3 < xhi then acc4 @ [ [ t3; yj ] ] else acc4
                            let t4 =  ( Val s * Val xi * Sqrt2 ).Eval ifl
                            let acc6 = if ylo < t4 && t4 < yhi then acc5 @ [ [ xi; t4 ] ] else acc5
                            acc6
                        ) acc1 [ifl.One; ifl.MinusOne]
                    ) acc [ylo; yhi]
            ) tests [xlo; xhi]
        let _, (amin, amax, bmin, bmax) =
            fWhile ( fun ( i, (amin, amax, bmin, bmax) ) -> i < updatedtests.Length)
                ( fun ( i, (amin, amax, bmin, bmax) ) ->
                let a, b = List.head updatedtests.[i], List.last updatedtests.[i]
                i + 1, (min a amin, max a amax, min b bmin, max b bmax)
                ) ( 0, (xlo, xhi, ylo, yhi) )
        let amin1 = if amin = ifl.Zero && inexQ env (fstBound xub) && inexQ env (sndBound xub) then (Val amin + From env.smallsubnormal / From 2.).Eval ifl else amin
        let bmin1 = if bmin = ifl.Zero && inexQ env (fstBound yub) && inexQ env (sndBound yub) then (Val bmin + From env.smallsubnormal / From 2.).Eval ifl else bmin
        let amax1 = if amax = ifl.Zero && inexQ env (fstBound xub) && inexQ env (sndBound xub) then (Val amax - From env.smallsubnormal / From 2.).Eval ifl else amax
        let bmax1 = if bmax = ifl.Zero && inexQ env (fstBound yub) && inexQ env (sndBound yub) then (Val bmax - From env.smallsubnormal / From 2.).Eval ifl else bmax
        [[x2u env amin1; x2u env bmin1]; [x2u env amax1;x2u env bmax1]]

    // Turn a unum into a guess, for imitation of float behavior.
    let guessu env u_ =
        ifUnumCompute env (fun u ->
        let ifl = env.ifl
        // If not already a general interval with exact endpoints, make it one.
        let g = unum2g_nc env u
        let (a,b),_ = g
        // Take care of trivial cases : NaN or an exact interval.
        if ifl.IsNaN a || ifl.IsNaN b then env.qNaNu
        elif a = b then x2u env a
        elif a = ifl.NegInf && b = ifl.PosInf then env.zerou
        // Average the endpoint values and convert to a unum.
        else
            let gu = x2u env ( ( (Val a + Val b) / From 2. ).Eval ifl )
            // If exact, we' re done. That' s the guess.
            let gu1 = if exQ env gu then gu
                      // else round to nearest even.
                      else
                        let gu2 = if env.ulpu &&& gu = 0UL then gu - env.ubitmask else gu + env.ubitmask
                        // Compress away the last zero in the fraction, since it is even.
                        if fsize_nc env gu2 = 1UL then gu2
                        else (( (floatmask_nc env gu2) &&& gu2 ) >>> 1) + ((env.efsizemask &&& gu2) - 1UL)
            gu1
        ) u_