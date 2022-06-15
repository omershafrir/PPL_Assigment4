import * as R from 'ramda'
// const R = require('ramda');

export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

export type Table<T> = Readonly<Record<string, Readonly<T>>>

export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}

// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {
    // optional initialization code
    const curr_table = sync();

    return {
        get(key: string): Promise<T> {
            return curr_table.then((table) => new Promise<T>((resolve, reject) => {  
                if (table[key] != undefined)
                    resolve(table[key])
                else{
                    reject(MISSING_KEY)
                }
            }))//.catch((MISSING_TABLE_SERVICE) => MISSING_TABLE_SERVICE) 

            
        },
        set(key: string, val: T): Promise<void> {
            return curr_table.then( (old_table) => new Promise<void>((resolve, reject) => {
                const new_table: Record<string, Readonly<T>> = old_table;
                new_table[key] = val;
                sync(new_table);
                resolve();  
                // reject(MISSING_KEY);
            })
            )//.catch((MISSING_TABLE_SERVICE) => MISSING_TABLE_SERVICE) 
            
        },
        delete(key: string): Promise<void> {
            return curr_table.then((old_table) =>new Promise<void>((resolve, reject) => {
                if (old_table[key] != undefined){
                    const new_table: Record<string, Readonly<T>> = old_table;
                    delete new_table[key];
                    sync(new_table);
                    resolve();
                }
                else
                    reject(MISSING_KEY)
            }))//.catch((MISSING_TABLE_SERVICE) => MISSING_TABLE_SERVICE) 
        }
    }
}


// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    
    const promises: Promise<T>[] = R.map((key: string) => store.get(key) , keys);
    return Promise.all(promises);

}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

const util = require('util')

export async function constructObjectFromTables (tables: TableServiceTable, ref: Reference) {
    const result = await func(tables,ref);
    // console.log("completed array is: ");
    // console.log(util.inspect( result , {showHidden: false, depth: null, colors: true}));
    // console.log(Object.fromEntries(result))


    return result;
    // const refTable:TableService<object> = tables[ref.table];
    // const refVal = await refTable.get(ref.key);
    // console.log("refTable: ", refTable)
    // console.log("refVal: ", refVal)
    // console.log("entries: " , (Object.entries(refVal)))
    // const entries = (Object.entries(refVal));
    // const mapped = R.map( (entry: any[]) => isReference(entry[1]) ? constructObjectFromTables(tables , entry[1] as Reference) : entry  , entries);


    // console.log("mapped: ", mapped)
    
    //return 


    // async function deref(ref: Reference) {
    // const refTable:TableService<object> = tables[ref.table];
    // const refVal = await refTable.get(ref.key);
    // console.log("refTable: ", refTable)
    // console.log("refVal: ", refVal)
    // console.log("entries: " , (Object.entries(refVal)))
    // const entries = (Object.entries(refVal));
    // const mapped = await R.map( (entry: any[]) => isReference(entry[1]) ? deref(tables , entry[1] as Reference) : entry  , entries);
    // }

    // return deref(ref)
}

export async function func(tables: TableServiceTable, ref: Reference): Promise<any>{
    if (tables[ref.table] === undefined)
        return   Promise.reject(MISSING_TABLE_SERVICE)

    const refTable:TableService<object> = tables[ref.table];
    const refVal = await refTable.get(ref.key);

    try{
        let entries = (Object.entries(refVal));
        for ( let entry in entries){
            if ( isReference(entries[entry][1]))
                entries[entry][1] = await func(tables , entries[entry][1]);
        }
        return Object.fromEntries(entries);
    }  catch{
        Promise.reject(MISSING_KEY)
    }
}

// export async function func(tables: TableServiceTable, ref: Reference): Promise<any[]>{
//     // console.log("sleeping for 5 secs...")
//     // await sleep(5000);
//     const refTable:TableService<object> = tables[ref.table];
//     const refVal = await refTable.get(ref.key);
//     // console.log("refTable: ", refTable)
//     // console.log("refVal: ", refVal)
//     // console.log("entries: " , (Object.entries(refVal)))
//     const entries = (Object.entries(refVal));
//     const mapped = R.map( (entry: any[]) => isReference(entry[1]) ? func(tables , entry[1] as Reference) : entry  , entries);

//     console.log("the refVal is: " , refVal , " \nmapped: ", mapped);
//     // Promise.all(mapped);
//     // console.log("PROMISE ", mapped);
//     return mapped;
// }

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        // for ( )
        let gen1 = g1();
        let gen2 = g2();
        let v1 = gen1.next();
        let v2 = gen2.next();

        while(!v1.done){
           while(!v2.done){
               yield [v1.value,v2.value];
               v2=gen2.next();
         }
         gen2=g2();
         v2=gen2.next();
         v1=gen1.next();
        }
    }
}
    
export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        // TODO implement!
        let gen1 = g1();
        let gen2 = g2();
        let v1 = gen1.next();
        let v2 = gen2.next();
        while(!v1.done && !v2.done){
            yield [v1.value,v2.value];
            v1 = gen1.next();
            v2 = gen2.next();
        }
        return  [v1.value,v2.value];
    }
}

// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {
    // optional initialization code

    let _table: Table<T> = await sync()
    type observersTable = Record<number, (table: Table<T>) => void  >;
    let observers: observersTable = {};
    let index = 0;

    const handleMutation = async (newTable: Table<T>): Promise<void> => {
        // TODO implement!
        if (optimistic){                    //each observer gets a call immediately when a change is requested.
            for (let i=0; i< index ; i++){  //if the mutation has failed, each observer should get a call with the previous table
                observers[i](newTable);
            }
            
        }
        else{           //each observer gets a call only after the mutation has succeded
            
        }
    }

    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        set(key: string, val: T): Promise<void> {
            const new_table: Record<string, Readonly<T>> = _table;
            new_table[key] = val;
            
            return handleMutation(new_table)
        },
        delete(key: string): Promise<void> {
            if (key in _table) {
                const new_table: Record<string, Readonly<T>> = _table;
                delete new_table[key];    
                return handleMutation(new_table)

            } else {
                throw MISSING_KEY
            }

        },

        subscribe(observer: (table: Table<T>) => void): void {
            observers[index] = observer;
            index++;
        }
    }
}