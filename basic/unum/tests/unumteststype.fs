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

module unumteststype =
    open unumtests
    open Microsoft.VisualStudio.TestTools.UnitTesting

    [<TestClass>]
    type unum64tests () =

        let tests = ``Tests from The End Of Error book`` ()
    
        [<TestMethod>]
        member x.``Bailey’s numerical nightmare (p. 184) with float (failing)`` () =
            Assert.IsTrue <| tests.``Bailey’s numerical nightmare (p. 184) with float (failing)`` ()

        [<TestMethod>]
        member x.``Bailey’s numerical nightmare (p. 184) with uboundDM on dfloat`` () =
            Assert.IsTrue <| tests.``Bailey’s numerical nightmare (p. 184) with uboundDM on dfloat`` ()

        [<TestMethod>]
        member x.``Bailey’s numerical nightmare (p. 184) with ubound on dfloat`` () =
            Assert.IsTrue <| tests.``Bailey’s numerical nightmare (p. 184) with ubound on dfloat`` ()
        [<TestMethod>]
        member x.``Bailey’s numerical nightmare (p. 184) with uboundg on dfloat`` () =
            Assert.IsTrue <| tests.``Bailey’s numerical nightmare (p. 184) with uboundg on dfloat`` ()

        [<TestMethod>]
        member x.``Jean-Michel Muller H function (p. 176) with ubound on dfloat`` () =
            Assert.IsTrue <| tests.``Jean-Michel Muller H function (p. 176) with ubound on dfloat`` ()

        [<TestMethod>]
        member x.``The wrath of Kahan (p. 173) with uboundg on dfloat`` () =
            Assert.IsTrue <| tests.``The wrath of Kahan (p. 173) with uboundg on dfloat`` ()

        [<TestMethod>]
        member x.``The quadratic formula (p. 181) with uboundDM on float`` () =
            Assert.IsTrue <| tests.``The quadratic formula (p. 181) with uboundDM on float`` ()

        [<TestMethod>]
        member x.``The smooth surprise with uboundg on float`` () =
            Assert.IsTrue <| tests.``The smooth surprise with uboundg on float`` ()
        
        //[<TestMethod>]
        //member x. () =
        //    Assert.IsTrue <| tests. ()
