# BidirectionalTypeSystem2

My second attempt at implementing a bidirectional type system for the lambda calculus

Based on [this paper](https://www.cl.cam.ac.uk/~nk480/bidir.pdf)
```bibtex
@article{dunfield2013complete,
  title={Complete and easy bidirectional typechecking for higher-rank polymorphism},
  author={Dunfield, Joshua and Krishnaswami, Neelakantan R},
  journal={ACM SIGPLAN Notices},
  volume={48},
  number={9},
  pages={429--442},
  year={2013},
  publisher={ACM New York, NY, USA}
}
```

---

grammar
```
expr : identifier 
     | "()"
     | "\" identifier "." expr
     | expr expr 
     | "(" expr "::" type ")"

type : "1"
     | lower_identifier
     | "forall" lower_identifier "." type
     | type "->" type
```
The language only has unit and lambdas, but you can still have higher
rank polymorphism be meaningful in such a simple system.