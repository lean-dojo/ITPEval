;; Statement-only formalization of Hundred Theorems artifact 100, "Descartes'
;; Rule of Signs": for a nonzero polynomial over an arbitrary strict ordered
;; commutative ring, the total multiplicity of its positive roots is at most
;; its number of coefficient sign variations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent an arbitrary ordered commutative
;; ring. No completeness or concrete real-number representation is needed.
(defstub ds100-carrier (x) t)
(defstub ds100-add-op (x y) t)
(defstub ds100-multiply-op (x y) t)
(defstub ds100-negate-op (x) t)
(defstub ds100-less-op (x y) t)

(defun ds100-member-p (x)
  (if (ds100-carrier x) t nil))

(defun ds100-add (x y)
  (ds100-add-op x y))

(defun ds100-mul (x y)
  (ds100-multiply-op x y))

(defun ds100-neg (x)
  (ds100-negate-op x))

(defun ds100-less (x y)
  (if (ds100-less-op x y) t nil))

(defun-sk ds100-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ds100-member-p x)
      (ds100-member-p y)
      (ds100-member-p z))
     (and
      (ds100-member-p (ds100-add x y))
      (ds100-member-p (ds100-mul x y))
      (ds100-member-p (ds100-neg x))
      (equal (ds100-add (ds100-add x y) z)
             (ds100-add x (ds100-add y z)))
      (equal (ds100-add x y) (ds100-add y x))
      (equal (ds100-add x zero) x)
      (equal (ds100-add x (ds100-neg x)) zero)
      (equal (ds100-mul (ds100-mul x y) z)
             (ds100-mul x (ds100-mul y z)))
      (equal (ds100-mul x y) (ds100-mul y x))
      (equal (ds100-mul x one) x)
      (equal
       (ds100-mul x (ds100-add y z))
       (ds100-add (ds100-mul x y)
                  (ds100-mul x z)))))))

(defun-sk ds100-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ds100-member-p x)
      (ds100-member-p y)
      (ds100-member-p z))
     (and
      (not (ds100-less x x))
      (or (equal x y)
          (ds100-less x y)
          (ds100-less y x))
      (implies
       (and (ds100-less x y)
            (ds100-less y z))
       (ds100-less x z))
      (implies
       (ds100-less x y)
       (ds100-less (ds100-add x z)
                   (ds100-add y z)))
      (implies
       (and (ds100-less zero x)
            (ds100-less zero y))
       (ds100-less zero (ds100-mul x y)))))))

(defun ds100-strict-ordered-commutative-ring-p (zero one)
  (and
   (ds100-member-p zero)
   (ds100-member-p one)
   (not (equal zero one))
   (ds100-less zero one)
   (ds100-ring-laws-p zero one)
   (ds100-order-laws-p zero)))

(defun ds100-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (ds100-member-p (car coefficients))
       (ds100-coefficient-list-p (cdr coefficients)))
    (equal coefficients nil)))

(defun ds100-nonzero-polynomial-p (zero coefficients)
  (if (consp coefficients)
      (or
       (not (equal (car coefficients) zero))
       (ds100-nonzero-polynomial-p zero (cdr coefficients)))
    nil))

(defun ds100-natural-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (ds100-add one
               (ds100-natural-value (- n 1) zero one))))

(defun ds100-polynomial-evaluate (coefficients x zero)
  (if (consp coefficients)
      (ds100-add
       (car coefficients)
       (ds100-mul
        x
        (ds100-polynomial-evaluate
         (cdr coefficients) x zero)))
    zero))

(defun ds100-polynomial-derivative-aux
    (coefficients degree zero one)
  (if (consp coefficients)
      (cons
       (ds100-mul
        (ds100-natural-value degree zero one)
        (car coefficients))
       (ds100-polynomial-derivative-aux
        (cdr coefficients) (+ degree 1) zero one))
    nil))

(defun ds100-polynomial-derivative (coefficients zero one)
  (if (consp coefficients)
      (ds100-polynomial-derivative-aux
       (cdr coefficients) 1 zero one)
    nil))

(defun ds100-iterated-derivative
    (count coefficients zero one)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      coefficients
    (ds100-iterated-derivative
     (- count 1)
     (ds100-polynomial-derivative coefficients zero one)
     zero one)))

(defun ds100-lower-derivatives-vanish-p
    (count coefficients root zero one)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (equal
      (ds100-polynomial-evaluate coefficients root zero)
      zero)
     (ds100-lower-derivatives-vanish-p
      (- count 1)
      (ds100-polynomial-derivative coefficients zero one)
      root zero one))))

(defun ds100-root-multiplicity-p
    (coefficients root multiplicity zero one)
  (and
   (posp multiplicity)
   (ds100-lower-derivatives-vanish-p
    multiplicity coefficients root zero one)
   (not
    (equal
     (ds100-polynomial-evaluate
      (ds100-iterated-derivative
       multiplicity coefficients zero one)
      root zero)
     zero))))

(defun ds100-opposite-sign-p (zero x y)
  (or
   (and (ds100-less x zero)
        (ds100-less zero y))
   (and (ds100-less y zero)
        (ds100-less zero x))))

(defun ds100-sign-variations-aux
    (zero coefficients previous have-previous)
  (if (consp coefficients)
      (let ((current (car coefficients)))
        (if (equal current zero)
            (ds100-sign-variations-aux
             zero (cdr coefficients) previous have-previous)
          (+
           (if (and have-previous
                    (ds100-opposite-sign-p
                     zero previous current))
               1
             0)
           (ds100-sign-variations-aux
            zero (cdr coefficients) current t))))
    0))

(defun ds100-sign-variations (zero coefficients)
  (ds100-sign-variations-aux
   zero coefficients zero nil))

;; Each root entry is the dotted pair (root . positive-multiplicity).
(defun ds100-root-entry-valid-p
    (entry coefficients zero one)
  (and
   (consp entry)
   (ds100-member-p (car entry))
   (ds100-less zero (car entry))
   (ds100-root-multiplicity-p
    coefficients (car entry) (cdr entry) zero one)))

(defun ds100-root-not-in-entries-p (root entries)
  (if (consp entries)
      (and
       (not (equal root (car (car entries))))
       (ds100-root-not-in-entries-p root (cdr entries)))
    (equal entries nil)))

(defun ds100-positive-root-list-p
    (entries coefficients zero one)
  (if (consp entries)
      (and
       (ds100-root-entry-valid-p
        (car entries) coefficients zero one)
       (ds100-root-not-in-entries-p
        (car (car entries)) (cdr entries))
       (ds100-positive-root-list-p
        (cdr entries) coefficients zero one))
    (equal entries nil)))

(defun ds100-root-present-p (root entries)
  (if (consp entries)
      (or
       (equal root (car (car entries)))
       (ds100-root-present-p root (cdr entries)))
    nil))

(defun-sk ds100-positive-root-list-complete-p
    (coefficients entries zero)
  (forall (root)
    (implies
     (ds100-member-p root)
     (iff
      (and
       (ds100-less zero root)
       (equal
        (ds100-polynomial-evaluate coefficients root zero)
        zero))
      (ds100-root-present-p root entries)))))

(defun ds100-total-multiplicity (entries)
  (if (consp entries)
      (+ (cdr (car entries))
         (ds100-total-multiplicity (cdr entries)))
    0))

(defun-sk ds100-descartes-conclusion-p
    (coefficients zero one)
  (exists (positive-roots)
    (and
     (true-listp positive-roots)
     (ds100-positive-root-list-p
      positive-roots coefficients zero one)
     (ds100-positive-root-list-complete-p
      coefficients positive-roots zero)
     (<=
      (ds100-total-multiplicity positive-roots)
      (ds100-sign-variations zero coefficients)))))

(defun-sk hundred-theorems-100-descartes-rule-of-signs-statement
    (zero one)
  (forall (coefficients)
    (implies
     (and
      (ds100-strict-ordered-commutative-ring-p zero one)
      (true-listp coefficients)
      (ds100-coefficient-list-p coefficients)
      (ds100-nonzero-polynomial-p zero coefficients))
     (ds100-descartes-conclusion-p
      coefficients zero one))))

(value-triple :itpeval-statement-checked)
:q
