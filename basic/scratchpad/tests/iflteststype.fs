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

module iflteststype =

    open ifl
    open ifltests
    open Microsoft.VisualStudio.TestTools.UnitTesting

    [<TestClass>]
    type iflteststype () =
        let iflF = SPFloat.IFloat
        let iflDF = SPDFloat.IFloat
        let tests = ``float based scratch pad tests`` ()
    
        [<TestMethod>]
        member x.``Run Polynomial test on float`` ()=
            Assert.IsTrue <| tests.Polynomial iflF
        [<TestMethod>]
        member x.``Run Machin's Formula for Pi test on float`` ()=
            Assert.IsTrue <| tests.``Machin's Formula for Pi`` iflF
        [<TestMethod>]
        member x.``Run Salamin-Brent Quadratic Formula for Pi test on float`` ()=
            Assert.IsTrue <| tests.``Salamin-Brent Quadratic Formula for Pi`` iflF
        [<TestMethod>]
        member x.``Run Borwein Quartic Formula for Pi test on float`` ()=
            Assert.IsTrue <| tests.``Borwein Quartic Formula for Pi`` iflF
        [<TestMethod>]
        member x.``Run Taylor Series Formula for E test on float`` ()=
            Assert.IsTrue <| tests.``Taylor Series Formula for E`` iflF
        [<TestMethod>]
        member x.``Run Taylor Series Formula for Log 2 test on float`` ()=
            Assert.IsTrue <| tests.``Taylor Series Formula for Log 2`` iflF
        [<TestMethod>]
        member x.``Run E square test on float`` ()=
            Assert.IsTrue <| tests.``E square`` iflF
        [<TestMethod>]
        member x.``Run Sanity check for sin / cos test on float`` ()=
            Assert.IsTrue <| tests.``Sanity check for sin / cos`` iflF
 

        [<TestMethod>]
        member x.``Run Polynomial test on dfloat`` ()=
            Assert.IsTrue <| tests.Polynomial iflDF
        [<TestMethod>]
        member x.``Run Machin's Formula for Pi test on dfloat`` ()=
            Assert.IsTrue <| tests.``Machin's Formula for Pi`` iflDF
        [<TestMethod>]
        member x.``Run Salamin-Brent Quadratic Formula for Pi test on dfloat`` ()=
            Assert.IsTrue <| tests.``Salamin-Brent Quadratic Formula for Pi`` iflDF
        [<TestMethod>]
        member x.``Run Borwein Quartic Formula for Pi test on dfloat`` ()=
            Assert.IsTrue <| tests.``Borwein Quartic Formula for Pi`` iflDF
        [<TestMethod>]
        member x.``Run Taylor Series Formula for E test on dfloat`` ()=
            Assert.IsTrue <| tests.``Taylor Series Formula for E`` iflDF
        [<TestMethod>]
        member x.``Run Taylor Series Formula for Log 2 test on dfloat`` ()=
            Assert.IsTrue <| tests.``Taylor Series Formula for Log 2`` iflDF
        [<TestMethod>]
        member x.``Run E square test on dfloat`` ()=
            Assert.IsTrue <| tests.``E square`` iflDF
        [<TestMethod>]
        member x.``Run Sanity check for sin / cos test on dfloat`` ()=
            Assert.IsTrue <| tests.``Sanity check for sin / cos`` iflDF
