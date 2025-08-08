(begin
  (let ((x 1) (y 2)) (+ x y))
  (begin (define (add x y) (+ x y)) (add 1 2))
  )

