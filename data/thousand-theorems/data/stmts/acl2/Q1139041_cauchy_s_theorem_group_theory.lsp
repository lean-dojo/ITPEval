;; Statement-only formalization of thousand-theorems corpus artifact Q1139041,
;; "Cauchy's theorem (group theory)": if a prime divides the cardinality of an
;; arbitrary finite group, then the group contains an element whose order is
;; that prime. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces present arbitrary group carriers and
;; operations. Every group law used by the statement is explicit below.

(defstub q1139041-element-p (group value) t)
(defstub q1139041-identity (group) t)
(defstub q1139041-multiply (group left right) t)
(defstub q1139041-inverse (group value) t)

(defun-sk q1139041-group-laws-p (group)
  (forall (a b c)
    (and
     (implies
      (q1139041-element-p group a)
      (and
       (q1139041-element-p
        group
        (q1139041-inverse group a))
       (equal
        (q1139041-multiply
         group a (q1139041-identity group))
        a)
       (equal
        (q1139041-multiply
         group (q1139041-identity group) a)
        a)
       (equal
        (q1139041-multiply
         group a (q1139041-inverse group a))
        (q1139041-identity group))
       (equal
        (q1139041-multiply
         group (q1139041-inverse group a) a)
        (q1139041-identity group))))
     (implies
      (and
       (q1139041-element-p group a)
       (q1139041-element-p group b))
      (q1139041-element-p
       group
       (q1139041-multiply group a b)))
     (implies
      (and
       (q1139041-element-p group a)
       (q1139041-element-p group b)
       (q1139041-element-p group c))
      (equal
       (q1139041-multiply
        group
        a
        (q1139041-multiply group b c))
       (q1139041-multiply
        group
        (q1139041-multiply group a b)
        c))))))

(defun q1139041-group-p (group)
  (and
   (q1139041-element-p
    group
    (q1139041-identity group))
   (q1139041-group-laws-p group)))

;; A duplicate-free exact enumeration is an internal witness that the
;; arbitrary carrier is finite. Its length is therefore the carrier's
;; cardinality, independently of the chosen enumeration order.

(defun-sk q1139041-enumerates-carrier-p
    (group enumeration)
  (forall (x)
    (iff
     (q1139041-element-p group x)
     (member-equal x enumeration))))

(defun q1139041-exact-finite-enumeration-p
    (group enumeration)
  (and
   (true-listp enumeration)
   (no-duplicatesp-equal enumeration)
   (q1139041-enumerates-carrier-p
    group enumeration)))

(defun q1139041-divides-p (divisor dividend)
  (and
   (natp divisor)
   (natp dividend)
   (if (equal divisor 0)
       (equal dividend 0)
     (equal (mod dividend divisor) 0))))

(defun-sk q1139041-prime-divisor-law-p (p)
  (forall (divisor)
    (implies
     (q1139041-divides-p divisor p)
     (or
      (equal divisor 1)
      (equal divisor p)))))

(defun q1139041-primep (p)
  (and
   (natp p)
   (< 1 p)
   (q1139041-prime-divisor-law-p p)))

(defun-sk q1139041-prime-divides-card-p (group p)
  (exists (enumeration)
    (and
     (q1139041-exact-finite-enumeration-p
      group enumeration)
     (q1139041-divides-p
      p
      (len enumeration)))))

;; The order predicate says exactly that p is the least positive exponent
;; taking the element to the identity.

(defun q1139041-power (group element exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q1139041-identity group)
    (q1139041-multiply
     group
     element
     (q1139041-power
      group element (- exponent 1)))))

(defun-sk q1139041-no-smaller-positive-power-p
    (group element p)
  (forall (exponent)
    (implies
     (and
      (natp exponent)
      (< 0 exponent)
      (< exponent p))
     (not
      (equal
       (q1139041-power
        group element exponent)
       (q1139041-identity group))))))

(defun q1139041-order-equals-p
    (group element p)
  (and
   (natp p)
   (< 0 p)
   (equal
    (q1139041-power group element p)
    (q1139041-identity group))
   (q1139041-no-smaller-positive-power-p
    group element p)))

(defun-sk q1139041-has-element-of-order-p (group p)
  (exists (element)
    (and
     (q1139041-element-p group element)
     (q1139041-order-equals-p
      group element p))))

(defun-sk
    thousand-theorems-q1139041-cauchys-theorem-group-theory-statement
    ()
  (forall (group p)
    (implies
     (and
      (q1139041-group-p group)
      (q1139041-primep p)
      (q1139041-prime-divides-card-p group p))
     (q1139041-has-element-of-order-p group p))))

(value-triple :itpeval-statement-checked)
:q
