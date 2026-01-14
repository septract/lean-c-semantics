Aims: 

* input: C code 
* output: Lean code representing the C semantics 

Approach: 

* Take the existing C semantics Cerberus https://github.com/rems-project/cerberus
* Run Cerberus, generating an AST for one of the internal IRs 
* Parse this IR in Lean 
* Define a semantics / interpreter in Lean for this IR 

Design goals: 

* Totally decoupled from Cerberus, doesn't require any new features 
* Highly trustworthy wrt the Cerberus semantics 
* Suitable for reasoning in Lean 
* Uses an existing Lean abstraction, for example Std.Do 

