;; Statement-only formalization of PutnamBench corpus artifact putnam_1965_b4:
;; the recurrence, convergence domain, and square-root limit of ratios of the
;; even and odd binomial sums. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source sequence has an explicit algebraic recurrence and explicit
;; square-root limit. It therefore needs field algebra, order, the
;; Archimedean property, and nonnegative square roots, but not quantification
;; over arbitrary subsets of the real line. Conservative generic symbols
;; preserve arbitrary scalar values without restricting them to ACL2
;; rationals or APPLY$-tame objects.

(defstub p65b4-scalar-p (x) t)
(defstub p65b4-add (x y) t)
(defstub p65b4-multiply (x y) t)
(defstub p65b4-negate (x) t)
(defstub p65b4-inverse (x) t)
(defstub p65b4-less (x y) t)
(defstub p65b4-square-root (x) t)
(defstub p65b4-archimedean-bound (x) t)

(defun p65b4-member-p (x)
  (if (p65b4-scalar-p x) t nil))

(defun p65b4-less-p (x y)
  (if (p65b4-less x y) t nil))

(defun p65b4-subtract (x y)
  (p65b4-add x (p65b4-negate y)))

(defun p65b4-divide (x y)
  (p65b4-multiply x (p65b4-inverse y)))

(defun p65b4-absolute-value (zero x)
  (if (p65b4-less-p x zero)
      (p65b4-negate x)
    x))

(defun p65b4-positive-p (zero x)
  (and
   (p65b4-member-p x)
   (p65b4-less-p zero x)))

(defun p65b4-nonnegative-p (zero x)
  (and
   (p65b4-member-p x)
   (not (p65b4-less-p x zero))))

(defun-sk p65b4-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p65b4-member-p x)
      (p65b4-member-p y)
      (p65b4-member-p z))
     (and
      (p65b4-member-p (p65b4-add x y))
      (p65b4-member-p (p65b4-multiply x y))
      (p65b4-member-p (p65b4-negate x))
      (p65b4-member-p (p65b4-inverse x))
      (equal
       (p65b4-add (p65b4-add x y) z)
       (p65b4-add x (p65b4-add y z)))
      (equal (p65b4-add x y) (p65b4-add y x))
      (equal (p65b4-add x zero) x)
      (equal (p65b4-add x (p65b4-negate x)) zero)
      (equal
       (p65b4-multiply (p65b4-multiply x y) z)
       (p65b4-multiply x (p65b4-multiply y z)))
      (equal (p65b4-multiply x y) (p65b4-multiply y x))
      (equal (p65b4-multiply x one) x)
      (implies
       (equal x zero)
       (equal (p65b4-inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p65b4-multiply x (p65b4-inverse x))
        one))
      (equal
       (p65b4-multiply x (p65b4-add y z))
       (p65b4-add
        (p65b4-multiply x y)
        (p65b4-multiply x z)))))))

(defun-sk p65b4-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p65b4-member-p x)
      (p65b4-member-p y)
      (p65b4-member-p z))
     (and
      (not (p65b4-less-p x x))
      (or
       (equal x y)
       (p65b4-less-p x y)
       (p65b4-less-p y x))
      (implies
       (and
        (p65b4-less-p x y)
        (p65b4-less-p y z))
       (p65b4-less-p x z))
      (implies
       (p65b4-less-p x y)
       (p65b4-less-p
        (p65b4-add x z)
        (p65b4-add y z)))
      (implies
       (and
        (p65b4-less-p zero x)
        (p65b4-less-p zero y))
       (p65b4-less-p
        zero
        (p65b4-multiply x y)))))))

(defun p65b4-natural-value (zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p65b4-add
     (p65b4-natural-value zero one (- n 1))
     one)))

(defun-sk p65b4-archimedean-law-p (zero one)
  (forall (x)
    (implies
     (p65b4-member-p x)
     (and
      (natp (p65b4-archimedean-bound x))
      (p65b4-less-p
       x
       (p65b4-natural-value
        zero one
        (p65b4-archimedean-bound x)))))))

(defun-sk p65b4-square-root-laws-p (zero)
  (forall (x)
    (implies
     (p65b4-nonnegative-p zero x)
     (and
      (p65b4-member-p (p65b4-square-root x))
      (not (p65b4-less-p (p65b4-square-root x) zero))
      (equal
       (p65b4-multiply
        (p65b4-square-root x)
        (p65b4-square-root x))
       x)))))

(defun p65b4-real-algebra-p (zero one)
  (and
   (p65b4-member-p zero)
   (p65b4-member-p one)
   (not (equal zero one))
   (p65b4-field-laws-p zero one)
   (p65b4-order-laws-p zero)
   (p65b4-less-p zero one)
   (p65b4-archimedean-law-p zero one)
   (p65b4-square-root-laws-p zero)))

;; Starting from (u_0,v_0)=(1,0), this update expands to the source's
;; even-indexed and odd-indexed binomial sums:
;;
;;   (u_(n+1),v_(n+1))=(u_n+x*v_n,u_n+v_n).
;;
;; The source only constrains positive indices, so fixing index zero does not
;; affect either convergence or the limit.

(defun p65b4-state (n x zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons one zero)
    (let* ((previous
            (p65b4-state (- n 1) x zero one))
           (u (car previous))
           (v (cdr previous)))
      (cons
       (p65b4-add u (p65b4-multiply x v))
       (p65b4-add u v)))))

(defun p65b4-u (n x zero one)
  (car (p65b4-state n x zero one)))

(defun p65b4-v (n x zero one)
  (cdr (p65b4-state n x zero one)))

(defun p65b4-f (n x zero one)
  (p65b4-divide
   (p65b4-u n x zero one)
   (p65b4-v n x zero one)))

(defun-sk p65b4-convergence-tail-p
    (zero one x limit epsilon cutoff)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= cutoff index))
     (p65b4-less-p
      (p65b4-absolute-value
       zero
       (p65b4-subtract
        (p65b4-f index x zero one)
        limit))
      epsilon))))

(defun-sk p65b4-convergence-cutoff-exists-p
    (zero one x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p65b4-convergence-tail-p
      zero one x limit epsilon cutoff))))

(defun-sk p65b4-converges-to-p (zero one x limit)
  (forall (epsilon)
    (implies
     (p65b4-positive-p zero epsilon)
     (p65b4-convergence-cutoff-exists-p
      zero one x limit epsilon))))

(defun-sk p65b4-limit-exists-p (zero one x)
  (exists (limit)
    (and
     (p65b4-member-p limit)
     (p65b4-converges-to-p zero one x limit))))

(defun-sk p65b4-recurrence-p (zero one)
  (forall (n x)
    (implies
     (and
      (posp n)
      (p65b4-member-p x))
     (let* ((v-n (p65b4-v n x zero one))
            (v-next (p65b4-v (+ n 1) x zero one))
            (f-n (p65b4-f n x zero one))
            (q-f-n (p65b4-add f-n one)))
       (implies
        (and
         (not (equal v-n zero))
         (not (equal v-next zero))
         (not (equal q-f-n zero)))
        (equal
         (p65b4-f (+ n 1) x zero one)
         (p65b4-divide
          (p65b4-add f-n x)
          q-f-n)))))))

(defun-sk p65b4-convergence-domain-p (zero one)
  (forall (x)
    (implies
     (p65b4-member-p x)
     (iff
      (p65b4-limit-exists-p zero one x)
      (p65b4-nonnegative-p zero x)))))

(defun-sk p65b4-square-root-limits-p (zero one)
  (forall (x)
    (implies
     (p65b4-nonnegative-p zero x)
     (p65b4-converges-to-p
      zero one x (p65b4-square-root x)))))

(defun putnambench-putnam-1965-b4-statement (zero one)
  (implies
   (p65b4-real-algebra-p zero one)
   (and
    (p65b4-recurrence-p zero one)
    (p65b4-convergence-domain-p zero one)
    (p65b4-square-root-limits-p zero one))))

(value-triple :itpeval-statement-checked)
:q
