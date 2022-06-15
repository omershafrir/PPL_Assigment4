import  * as TEXP from "./L5/TExp";
import  * as Typecheck from "./L5/L5-typecheck";
import  * as AST from "./L5/L5-ast";

import { equals, filter, flatten, includes, map, intersection, zipWith, reduce, sort } from 'ramda';
import * as Res from "./shared/result";
import { initTEnv, typeofProgram } from "./L5/L5-typecheck";
// import  * as TEXP from "./L5/TExp";
// import  * as TEXP from "./L5/TExp";


const prog1 = `
(L51 
    (define-type Shape
        (circle (radius : number))
        (rectangle (width : number)
                (height : number)))
    (define (s : circle) (make-circle 1))
    (type-case Shape s
        (circle (r) (make-circle (* 2 r)))
        (rectangle (w h) (make-circle (+ w h))))
)
`

const prog2 = `
(L51 
    (define-type Shape
        (circle (radius : number))
        (rectangle (width : number)
                (height : number)))
    (define (s : circle) (make-circle 1))
    (type-case circle s
        (circle (r) (make-rectangle r r))
        (rectangle (w h) (make-circle (+ w h))))
)
`
const circle = TEXP.makeUserDefinedNameTExp('circle');
const Shape = TEXP.makeUserDefinedNameTExp('Shape');

const p1 = AST.parseL51(prog1);
const p2 = AST.parseL51(prog2);


const t1 = Res.bind (p1 , (pr: AST.Program) => typeofProgram(pr, initTEnv(pr), pr));
const t2 = Res.bind (p2 , (pr: AST.Program) => typeofProgram(pr, initTEnv(pr), pr));

console.log("TEST1:")
console.log (JSON.stringify(t1))
console.log (JSON.stringify(circle))
console.log()
console.log("TEST2:")
console.log (JSON.stringify(t2))
console.log (JSON.stringify(Shape))





