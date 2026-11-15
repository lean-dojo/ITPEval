;; Statement-only formalization of PutnamBench artifact putnam_1992_b6:
;; a family of n-by-n matrices satisfying the signed closure and
;; anticommutation hypotheses has at most n^2 members. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Matrices are ordinary finite ACL2 lists. The scalar operations and the
;; matrix-family predicate are conservative generic symbols, which is ACL2's
;; native way to state a theorem uniformly over an arbitrary field and an
;; arbitrary set. No function codes, axioms, or bounded surrogate family are
;; introduced.
(defstub p1992b6-scalar-p (x) t)
(defstub p1992b6-add-op (x y) t)
(defstub p1992b6-multiply-op (x y) t)
(defstub p1992b6-negate-op (x) t)
(defstub p1992b6-inverse-op (x) t)
(defstub p1992b6-family-member-p (matrix) t)

(defun p1992b6-add (x y)
  (p1992b6-add-op x y))

(defun p1992b6-mul (x y)
  (p1992b6-multiply-op x y))

(defun p1992b6-neg (x)
  (p1992b6-negate-op x))

(defun p1992b6-inv (x)
  (p1992b6-inverse-op x))

(defun-sk p1992b6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1992b6-scalar-p x)
      (p1992b6-scalar-p y)
      (p1992b6-scalar-p z))
     (and
      (p1992b6-scalar-p (p1992b6-add x y))
      (p1992b6-scalar-p (p1992b6-mul x y))
      (p1992b6-scalar-p (p1992b6-neg x))
      (implies
       (not (equal x zero))
       (p1992b6-scalar-p (p1992b6-inv x)))
      (equal (p1992b6-add (p1992b6-add x y) z)
             (p1992b6-add x (p1992b6-add y z)))
      (equal (p1992b6-add x y)
             (p1992b6-add y x))
      (equal (p1992b6-add x zero) x)
      (equal (p1992b6-add x (p1992b6-neg x)) zero)
      (equal (p1992b6-mul (p1992b6-mul x y) z)
             (p1992b6-mul x (p1992b6-mul y z)))
      (equal (p1992b6-mul x y)
             (p1992b6-mul y x))
      (equal (p1992b6-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1992b6-mul x (p1992b6-inv x)) one))
      (equal
       (p1992b6-mul x (p1992b6-add y z))
       (p1992b6-add (p1992b6-mul x y)
                    (p1992b6-mul x z)))))))

(defun p1992b6-field-p (zero one)
  (and
   (p1992b6-scalar-p zero)
   (p1992b6-scalar-p one)
   (not (equal zero one))
   ;; The real field has characteristic zero; only characteristic two is a
   ;; material degeneracy for the signed matrix hypotheses.
   (not (equal (p1992b6-add one one) zero))
   (p1992b6-field-laws-p zero one)))

(defun p1992b6-scalar-list-p (row n)
  (if (zp n)
      (endp row)
    (and
     (consp row)
     (p1992b6-scalar-p (car row))
     (p1992b6-scalar-list-p (cdr row) (1- n)))))

(defun p1992b6-matrix-p (matrix n)
  (if (zp n)
      (endp matrix)
    (and
     (consp matrix)
     (p1992b6-scalar-list-p (car matrix) n)
     (p1992b6-matrix-p (cdr matrix) (1- n)))))

(defun p1992b6-dot-product (left right row column remaining zero)
  (if (zp remaining)
      zero
    (p1992b6-add
     (p1992b6-mul
      (nth (- (len (car left)) remaining) (nth row left))
      (nth column
           (nth (- (len right) remaining) right)))
     (p1992b6-dot-product
      left right row column (1- remaining) zero))))

(defun p1992b6-product-row-aux
    (left right row column remaining n zero)
  (if (zp remaining)
      nil
    (cons
     (p1992b6-dot-product left right row column n zero)
     (p1992b6-product-row-aux
      left right row (1+ column) (1- remaining) n zero))))

(defun p1992b6-product-matrix-aux
    (left right row remaining n zero)
  (if (zp remaining)
      nil
    (cons
     (p1992b6-product-row-aux left right row 0 n n zero)
     (p1992b6-product-matrix-aux
      left right (1+ row) (1- remaining) n zero))))

(defun p1992b6-product (left right n zero)
  (p1992b6-product-matrix-aux left right 0 n n zero))

(defun p1992b6-negate-row (row)
  (if (endp row)
      nil
    (cons
     (p1992b6-neg (car row))
     (p1992b6-negate-row (cdr row)))))

(defun p1992b6-negate-matrix (matrix)
  (if (endp matrix)
      nil
    (cons
     (p1992b6-negate-row (car matrix))
     (p1992b6-negate-matrix (cdr matrix)))))

(defun p1992b6-identity-row-aux
    (row column remaining zero one)
  (if (zp remaining)
      nil
    (cons
     (if (equal row column) one zero)
     (p1992b6-identity-row-aux
      row (1+ column) (1- remaining) zero one))))

(defun p1992b6-identity-aux
    (row remaining n zero one)
  (if (zp remaining)
      nil
    (cons
     (p1992b6-identity-row-aux row 0 n zero one)
     (p1992b6-identity-aux
      (1+ row) (1- remaining) n zero one))))

(defun p1992b6-identity (n zero one)
  (p1992b6-identity-aux 0 n n zero one))

(defun p1992b6-exclusive-or (left right)
  (if left (not right) (if right t nil)))

(defun-sk p1992b6-signed-closure-p (n zero)
  (forall (a b)
    (implies
     (and
      (p1992b6-matrix-p a n)
      (p1992b6-matrix-p b n)
      (p1992b6-family-member-p a)
      (p1992b6-family-member-p b))
     (let* ((ab (p1992b6-product a b n zero))
            (negative-ab (p1992b6-negate-matrix ab)))
       (p1992b6-exclusive-or
        (p1992b6-family-member-p ab)
        (p1992b6-family-member-p negative-ab))))))

(defun-sk p1992b6-commute-or-anticommute-p (n zero)
  (forall (a b)
    (implies
     (and
      (p1992b6-matrix-p a n)
      (p1992b6-matrix-p b n)
      (p1992b6-family-member-p a)
      (p1992b6-family-member-p b))
     (let ((ab (p1992b6-product a b n zero))
           (ba (p1992b6-product b a n zero)))
       (or
        (equal ab ba)
        (equal ab (p1992b6-negate-matrix ba)))))))

(defun-sk p1992b6-anticommuting-witness-exists-p
    (a n zero)
  (exists (b)
    (and
     (p1992b6-matrix-p b n)
     (p1992b6-family-member-p b)
     (equal
      (p1992b6-product a b n zero)
      (p1992b6-negate-matrix
       (p1992b6-product b a n zero))))))

(defun-sk p1992b6-nonidentity-anticommutes-p
    (n zero one)
  (forall (a)
    (implies
     (and
      (p1992b6-matrix-p a n)
      (p1992b6-family-member-p a)
      (not (equal a (p1992b6-identity n zero one))))
     (p1992b6-anticommuting-witness-exists-p a n zero))))

(defun p1992b6-family-list-p (matrices n)
  (if (endp matrices)
      t
    (and
     (p1992b6-matrix-p (car matrices) n)
     (p1992b6-family-member-p (car matrices))
     (p1992b6-family-list-p (cdr matrices) n))))

(defun-sk p1992b6-too-many-members-p (n)
  (exists (matrices)
    (and
     (true-listp matrices)
     (equal (len matrices) (1+ (* n n)))
     (no-duplicatesp-equal matrices)
     (p1992b6-family-list-p matrices n))))

(defun putnambench-putnam-1992-b6-statement
    (n zero one)
  (implies
   (and
    (natp n)
    (< 0 n)
    (p1992b6-field-p zero one)
    (p1992b6-family-member-p
     (p1992b6-identity n zero one))
    (p1992b6-signed-closure-p n zero)
    (p1992b6-commute-or-anticommute-p n zero)
    (p1992b6-nonidentity-anticommutes-p n zero one))
   (not (p1992b6-too-many-members-p n))))

(value-triple :itpeval-statement-checked)
:q
