;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_b6:
;; for square matrices A, B, C, and D over an arbitrary field, symmetry of
;; A*B^T and C*D^T together with A*D^T-B*C^T=I implies
;; A^T*D-C^T*B=I. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative generic symbols represent an arbitrary field and four
;; arbitrary matrix-entry functions. No APPLY$ executability restriction is
;; imposed on the field operations or matrices.

(defstub putnam-1986-b6-carrier (x) t)
(defstub putnam-1986-b6-add (x y) t)
(defstub putnam-1986-b6-multiply (x y) t)
(defstub putnam-1986-b6-negate (x) t)
(defstub putnam-1986-b6-inverse (x) t)
(defstub putnam-1986-b6-a (i j) t)
(defstub putnam-1986-b6-b (i j) t)
(defstub putnam-1986-b6-c (i j) t)
(defstub putnam-1986-b6-d (i j) t)

(defun putnam-1986-b6-member-p (x)
  (if (putnam-1986-b6-carrier x) t nil))

(defun-sk putnam-1986-b6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1986-b6-member-p x)
      (putnam-1986-b6-member-p y)
      (putnam-1986-b6-member-p z))
     (and
      (putnam-1986-b6-member-p
       (putnam-1986-b6-add x y))
      (putnam-1986-b6-member-p
       (putnam-1986-b6-multiply x y))
      (putnam-1986-b6-member-p
       (putnam-1986-b6-negate x))
      (putnam-1986-b6-member-p
       (putnam-1986-b6-inverse x))
      (equal
       (putnam-1986-b6-add
        (putnam-1986-b6-add x y)
        z)
       (putnam-1986-b6-add
        x
        (putnam-1986-b6-add y z)))
      (equal
       (putnam-1986-b6-multiply
        (putnam-1986-b6-multiply x y)
        z)
       (putnam-1986-b6-multiply
        x
        (putnam-1986-b6-multiply y z)))
      (equal
       (putnam-1986-b6-add x y)
       (putnam-1986-b6-add y x))
      (equal
       (putnam-1986-b6-multiply x y)
       (putnam-1986-b6-multiply y x))
      (equal
       (putnam-1986-b6-add x zero)
       x)
      (equal
       (putnam-1986-b6-add
        x
        (putnam-1986-b6-negate x))
       zero)
      (equal
       (putnam-1986-b6-multiply x one)
       x)
      (implies
       (equal x zero)
       (equal
        (putnam-1986-b6-inverse x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (putnam-1986-b6-multiply
         x
         (putnam-1986-b6-inverse x))
        one))
      (equal
       (putnam-1986-b6-multiply
        x
        (putnam-1986-b6-add y z))
       (putnam-1986-b6-add
        (putnam-1986-b6-multiply x y)
        (putnam-1986-b6-multiply x z)))))))

(defun-sk putnam-1986-b6-matrix-entries-p (n)
  (forall (i j)
    (implies
     (and (natp i) (< i n)
          (natp j) (< j n))
     (and
      (putnam-1986-b6-member-p
       (putnam-1986-b6-a i j))
      (putnam-1986-b6-member-p
       (putnam-1986-b6-b i j))
      (putnam-1986-b6-member-p
       (putnam-1986-b6-c i j))
      (putnam-1986-b6-member-p
       (putnam-1986-b6-d i j))))))

(defun putnam-1986-b6-abt-sum (zero i j k count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1986-b6-add
     (putnam-1986-b6-multiply
      (putnam-1986-b6-a i k)
      (putnam-1986-b6-b j k))
     (putnam-1986-b6-abt-sum
      zero i j (+ 1 k) (- count 1)))))

(defun putnam-1986-b6-cdt-sum (zero i j k count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1986-b6-add
     (putnam-1986-b6-multiply
      (putnam-1986-b6-c i k)
      (putnam-1986-b6-d j k))
     (putnam-1986-b6-cdt-sum
      zero i j (+ 1 k) (- count 1)))))

(defun putnam-1986-b6-adt-sum (zero i j k count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1986-b6-add
     (putnam-1986-b6-multiply
      (putnam-1986-b6-a i k)
      (putnam-1986-b6-d j k))
     (putnam-1986-b6-adt-sum
      zero i j (+ 1 k) (- count 1)))))

(defun putnam-1986-b6-bct-sum (zero i j k count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1986-b6-add
     (putnam-1986-b6-multiply
      (putnam-1986-b6-b i k)
      (putnam-1986-b6-c j k))
     (putnam-1986-b6-bct-sum
      zero i j (+ 1 k) (- count 1)))))

(defun putnam-1986-b6-atd-sum (zero i j k count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1986-b6-add
     (putnam-1986-b6-multiply
      (putnam-1986-b6-a k i)
      (putnam-1986-b6-d k j))
     (putnam-1986-b6-atd-sum
      zero i j (+ 1 k) (- count 1)))))

(defun putnam-1986-b6-ctb-sum (zero i j k count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1986-b6-add
     (putnam-1986-b6-multiply
      (putnam-1986-b6-c k i)
      (putnam-1986-b6-b k j))
     (putnam-1986-b6-ctb-sum
      zero i j (+ 1 k) (- count 1)))))

(defun putnam-1986-b6-identity-entry (zero one i j)
  (if (equal i j) one zero))

(defun-sk putnam-1986-b6-symmetric-products-p (n zero)
  (forall (i j)
    (implies
     (and (natp i) (< i n)
          (natp j) (< j n))
     (and
      (equal
       (putnam-1986-b6-abt-sum zero i j 0 n)
       (putnam-1986-b6-abt-sum zero j i 0 n))
      (equal
       (putnam-1986-b6-cdt-sum zero i j 0 n)
       (putnam-1986-b6-cdt-sum zero j i 0 n))))))

(defun-sk putnam-1986-b6-right-identity-p (n zero one)
  (forall (i j)
    (implies
     (and (natp i) (< i n)
          (natp j) (< j n))
     (equal
      (putnam-1986-b6-add
       (putnam-1986-b6-adt-sum zero i j 0 n)
       (putnam-1986-b6-negate
        (putnam-1986-b6-bct-sum zero i j 0 n)))
      (putnam-1986-b6-identity-entry
       zero one i j)))))

(defun-sk putnam-1986-b6-left-identity-p (n zero one)
  (forall (i j)
    (implies
     (and (natp i) (< i n)
          (natp j) (< j n))
     (equal
      (putnam-1986-b6-add
       (putnam-1986-b6-atd-sum zero i j 0 n)
       (putnam-1986-b6-negate
        (putnam-1986-b6-ctb-sum zero i j 0 n)))
      (putnam-1986-b6-identity-entry
       zero one i j)))))

(defun-sk putnambench-putnam-1986-b6-statement ()
  (forall (n zero one)
    (implies
     (and
      (natp n)
      (< 0 n)
      (putnam-1986-b6-member-p zero)
      (putnam-1986-b6-member-p one)
      (not (equal zero one))
      (putnam-1986-b6-field-laws-p zero one)
      (putnam-1986-b6-matrix-entries-p n)
      (putnam-1986-b6-symmetric-products-p n zero)
      (putnam-1986-b6-right-identity-p n zero one))
     (putnam-1986-b6-left-identity-p
      n zero one))))

(value-triple :itpeval-statement-checked)
:q
