;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_484:
;; in the real numbers, the quotient ln(27) / ln(3) equals 3. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present the real field, its rational embedding, and
;; its natural logarithm. The statement predicate below makes all required
;; field, order, embedding, and logarithm laws explicit.

(defstub mathd-algebra-484-real-p (value) t)
(defstub mathd-algebra-484-zero () t)
(defstub mathd-algebra-484-one () t)
(defstub mathd-algebra-484-add (left right) t)
(defstub mathd-algebra-484-multiply (left right) t)
(defstub mathd-algebra-484-negate (value) t)
(defstub mathd-algebra-484-inverse (value) t)
(defstub mathd-algebra-484-less (left right) t)
(defstub mathd-algebra-484-of-rational (value) t)
(defstub mathd-algebra-484-natural-log (value) t)

(defun mathd-algebra-484-divide (numerator denominator)
  (mathd-algebra-484-multiply
   numerator
   (mathd-algebra-484-inverse denominator)))

(defun-sk mathd-algebra-484-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (mathd-algebra-484-real-p x)
      (mathd-algebra-484-real-p y)
      (mathd-algebra-484-real-p z))
     (and
      (mathd-algebra-484-real-p
       (mathd-algebra-484-add x y))
      (mathd-algebra-484-real-p
       (mathd-algebra-484-multiply x y))
      (mathd-algebra-484-real-p
       (mathd-algebra-484-negate x))
      (mathd-algebra-484-real-p
       (mathd-algebra-484-inverse x))
      (equal
       (mathd-algebra-484-add
        (mathd-algebra-484-add x y)
        z)
       (mathd-algebra-484-add
        x
        (mathd-algebra-484-add y z)))
      (equal
       (mathd-algebra-484-add x y)
       (mathd-algebra-484-add y x))
      (equal
       (mathd-algebra-484-add
        x
        (mathd-algebra-484-zero))
       x)
      (equal
       (mathd-algebra-484-add
        x
        (mathd-algebra-484-negate x))
       (mathd-algebra-484-zero))
      (equal
       (mathd-algebra-484-multiply
        (mathd-algebra-484-multiply x y)
        z)
       (mathd-algebra-484-multiply
        x
        (mathd-algebra-484-multiply y z)))
      (equal
       (mathd-algebra-484-multiply x y)
       (mathd-algebra-484-multiply y x))
      (equal
       (mathd-algebra-484-multiply
        x
        (mathd-algebra-484-one))
       x)
      (implies
       (equal x (mathd-algebra-484-zero))
       (equal
        (mathd-algebra-484-inverse x)
        (mathd-algebra-484-zero)))
      (implies
       (not (equal x (mathd-algebra-484-zero)))
       (equal
        (mathd-algebra-484-multiply
         x
         (mathd-algebra-484-inverse x))
        (mathd-algebra-484-one)))
      (equal
       (mathd-algebra-484-multiply
        x
        (mathd-algebra-484-add y z))
       (mathd-algebra-484-add
        (mathd-algebra-484-multiply x y)
        (mathd-algebra-484-multiply x z)))))))

(defun-sk mathd-algebra-484-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (mathd-algebra-484-real-p x)
      (mathd-algebra-484-real-p y)
      (mathd-algebra-484-real-p z))
     (and
      (not (mathd-algebra-484-less x x))
      (or
       (equal x y)
       (mathd-algebra-484-less x y)
       (mathd-algebra-484-less y x))
      (implies
       (and
        (mathd-algebra-484-less x y)
        (mathd-algebra-484-less y z))
       (mathd-algebra-484-less x z))
      (implies
       (mathd-algebra-484-less x y)
       (mathd-algebra-484-less
        (mathd-algebra-484-add x z)
        (mathd-algebra-484-add y z)))
      (implies
       (and
        (mathd-algebra-484-less
         (mathd-algebra-484-zero)
         x)
        (mathd-algebra-484-less
         (mathd-algebra-484-zero)
         y))
       (mathd-algebra-484-less
        (mathd-algebra-484-zero)
        (mathd-algebra-484-multiply x y)))))))

(defun-sk mathd-algebra-484-rational-embedding-laws-p ()
  (forall (p q)
    (implies
     (and (rationalp p)
          (rationalp q))
     (and
      (mathd-algebra-484-real-p
       (mathd-algebra-484-of-rational p))
      (mathd-algebra-484-real-p
       (mathd-algebra-484-of-rational q))
      (equal
       (mathd-algebra-484-of-rational 0)
       (mathd-algebra-484-zero))
      (equal
       (mathd-algebra-484-of-rational 1)
       (mathd-algebra-484-one))
      (equal
       (mathd-algebra-484-of-rational (+ p q))
       (mathd-algebra-484-add
        (mathd-algebra-484-of-rational p)
        (mathd-algebra-484-of-rational q)))
      (equal
       (mathd-algebra-484-of-rational (* p q))
       (mathd-algebra-484-multiply
        (mathd-algebra-484-of-rational p)
        (mathd-algebra-484-of-rational q)))
      (equal
       (mathd-algebra-484-of-rational (- p))
       (mathd-algebra-484-negate
        (mathd-algebra-484-of-rational p)))
      (iff
       (equal p q)
       (equal
        (mathd-algebra-484-of-rational p)
        (mathd-algebra-484-of-rational q)))
      (iff
       (< p q)
       (mathd-algebra-484-less
        (mathd-algebra-484-of-rational p)
        (mathd-algebra-484-of-rational q)))))))

(defun-sk mathd-algebra-484-natural-log-laws-p ()
  (forall (p q)
    (implies
     (and (rationalp p)
          (rationalp q))
     (and
      (implies
       (< 0 p)
       (mathd-algebra-484-real-p
        (mathd-algebra-484-natural-log
         (mathd-algebra-484-of-rational p))))
      (implies
       (and (< 0 p)
            (< 0 q))
       (equal
        (mathd-algebra-484-natural-log
         (mathd-algebra-484-of-rational (* p q)))
        (mathd-algebra-484-add
         (mathd-algebra-484-natural-log
          (mathd-algebra-484-of-rational p))
         (mathd-algebra-484-natural-log
          (mathd-algebra-484-of-rational q)))))
      (implies
       (< 1 p)
       (mathd-algebra-484-less
        (mathd-algebra-484-zero)
        (mathd-algebra-484-natural-log
         (mathd-algebra-484-of-rational p))))))))

(defun mathd-algebra-484-real-log-context-p ()
  (and
   (mathd-algebra-484-real-p
    (mathd-algebra-484-zero))
   (mathd-algebra-484-real-p
    (mathd-algebra-484-one))
   (not
    (equal
     (mathd-algebra-484-zero)
     (mathd-algebra-484-one)))
   (mathd-algebra-484-less
    (mathd-algebra-484-zero)
    (mathd-algebra-484-one))
   (mathd-algebra-484-field-laws-p)
   (mathd-algebra-484-order-laws-p)
   (mathd-algebra-484-rational-embedding-laws-p)
   (mathd-algebra-484-natural-log-laws-p)))

(defun mathd-algebra-484-statement ()
  (implies
   (mathd-algebra-484-real-log-context-p)
   (equal
    (mathd-algebra-484-divide
     (mathd-algebra-484-natural-log
      (mathd-algebra-484-of-rational 27))
     (mathd-algebra-484-natural-log
      (mathd-algebra-484-of-rational 3)))
    (mathd-algebra-484-of-rational 3))))

(value-triple :itpeval-statement-checked)
:q
