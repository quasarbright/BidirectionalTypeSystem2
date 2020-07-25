# BidirectionalTypeSystem2

My second attempt at implementing a bidirectional type system for the lambda calculus

Based on [this paper](https://dl.acm.org/doi/abs/10.1145/2544174.2500582?casa_token=S8NK3n32ikQAAAAA:DhVf6mor9v9hCiw1QTKyxALYiWYDwt3whcNg6faC351KLdeCkZv8zOc0G-ZOUvOMU_AZKQhqPEcE)
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
     | "1"
     | "\" identifier "." expr
     | expr expr 
     | "(" expr "::" type ")"

type
```