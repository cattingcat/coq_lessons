# SSReflect 

## Notes

### Unfold fib / fold fib_f
```
rewrite /(fib) -/(fib_f ). 
```

### Apply PQequiv to top of the goal
```
 move/PQequiv=> HQab.
```

### Apply to the goal
```
apply/PQequiv.
```

### Apply reflect view
```
apply/eqnP.
```

### Specific eqn func for nats to generic == operator
```
rewrite eqnE.
```



## An introduction to small scale reflection in Coq
https://hal.inria.fr/inria-00515548v4/document

## Cheatsheet
http://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/cheatsheet.pdf