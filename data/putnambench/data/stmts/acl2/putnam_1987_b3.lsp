;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_b3:
;; over any field of characteristic not two, the unit circle is the point
;; (1,0) together with its standard rational parametrization. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; DEFSTUB introduces conservative generic function symbols. The field is not
;; restricted to an APPLY$-executable presentation.

(defstub putnam-1987-b3-carrier (x) t)
(defstub putnam-1987-b3-add (x y) t)
(defstub putnam-1987-b3-multiply (x y) t)
(defstub putnam-1987-b3-negate (x) t)
(defstub putnam-1987-b3-inverse (x) t)

(defun putnam-1987-b3-member-p (x)
  (if (putnam-1987-b3-carrier x) t nil))

(defun putnam-1987-b3-subtract (x y)
  (putnam-1987-b3-add
   x
   (putnam-1987-b3-negate y)))

(defun putnam-1987-b3-divide (x y)
  (putnam-1987-b3-multiply
   x
   (putnam-1987-b3-inverse y)))

(defun-sk putnam-1987-b3-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1987-b3-member-p x)
      (putnam-1987-b3-member-p y)
      (putnam-1987-b3-member-p z))
     (and
      (putnam-1987-b3-member-p
       (putnam-1987-b3-add x y))
      (putnam-1987-b3-member-p
       (putnam-1987-b3-multiply x y))
      (putnam-1987-b3-member-p
       (putnam-1987-b3-negate x))
      (putnam-1987-b3-member-p
       (putnam-1987-b3-inverse x))
      (equal
       (putnam-1987-b3-add
        (putnam-1987-b3-add x y)
        z)
       (putnam-1987-b3-add
        x
        (putnam-1987-b3-add y z)))
      (equal
       (putnam-1987-b3-multiply
        (putnam-1987-b3-multiply x y)
        z)
       (putnam-1987-b3-multiply
        x
        (putnam-1987-b3-multiply y z)))
      (equal
       (putnam-1987-b3-add x y)
       (putnam-1987-b3-add y x))
      (equal
       (putnam-1987-b3-multiply x y)
       (putnam-1987-b3-multiply y x))
      (equal
       (putnam-1987-b3-add x zero)
       x)
      (equal
       (putnam-1987-b3-add
        x
        (putnam-1987-b3-negate x))
       zero)
      (equal
       (putnam-1987-b3-multiply x one)
       x)
      (implies
       (equal x zero)
       (equal
        (putnam-1987-b3-inverse x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (putnam-1987-b3-multiply
         x
         (putnam-1987-b3-inverse x))
        one))
      (equal
       (putnam-1987-b3-multiply
        x
        (putnam-1987-b3-add y z))
       (putnam-1987-b3-add
        (putnam-1987-b3-multiply x y)
        (putnam-1987-b3-multiply x z)))))))

(defun putnam-1987-b3-circle-point-p (one x y)
  (equal
   (putnam-1987-b3-add
    (putnam-1987-b3-multiply x x)
    (putnam-1987-b3-multiply y y))
   one))

(defun-sk putnam-1987-b3-parameter-exists-p
    (zero one x y)
  (exists (r)
    (let* ((r-square
            (putnam-1987-b3-multiply r r))
           (denominator
            (putnam-1987-b3-add r-square one))
           (minus-one
            (putnam-1987-b3-negate one)))
      (and
       (putnam-1987-b3-member-p r)
       (not (equal r-square minus-one))
       (equal
        x
        (putnam-1987-b3-divide
         (putnam-1987-b3-subtract r-square one)
         denominator))
       (equal
        y
        (putnam-1987-b3-divide
         (putnam-1987-b3-multiply
          (putnam-1987-b3-add one one)
          r)
         denominator))))))

(defun-sk putnam-1987-b3-circle-characterization-p
    (zero one)
  (forall (x y)
    (implies
     (and
      (putnam-1987-b3-member-p x)
      (putnam-1987-b3-member-p y))
     (equal
      (putnam-1987-b3-circle-point-p one x y)
      (or
       (and
        (equal x one)
        (equal y zero))
       (putnam-1987-b3-parameter-exists-p
        zero one x y))))))

(defun-sk putnambench-putnam-1987-b3-statement ()
  (forall (zero one)
    (implies
     (and
      (putnam-1987-b3-member-p zero)
      (putnam-1987-b3-member-p one)
      (not (equal zero one))
      (not
       (equal
        (putnam-1987-b3-add one one)
        zero))
      (putnam-1987-b3-field-laws-p zero one))
     (putnam-1987-b3-circle-characterization-p
      zero one))))

(value-triple :itpeval-statement-checked)
:q
