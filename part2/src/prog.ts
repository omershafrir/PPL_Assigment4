
const fruit = async(name: string) =>{
    const fruits:{[key:string] : string} = {
        'apple': 'APPLE' , 
        'banana': 'BANANA'
    }

    return Promise.resolve(fruits[name]);
}

const makeSmoothie = async() =>{
    const a = await fruit('apple')
    const b = await fruit('banana')
    return [a,b];
}   

// makeSmoothie().then(console.log)

// console.log(makeSmoothie())






function countTo(n: number) {
    return function* (): Generator<number> {
        for (let i = 1; i <= n; i++) {
            yield i
        }
    }
}

let x = countTo(3);
let v = x();


console.log(v.next().value);
console.log(v.next().value);
console.log(v.next().value);
console.log(v.next().value);
console.log(v.next().value);


