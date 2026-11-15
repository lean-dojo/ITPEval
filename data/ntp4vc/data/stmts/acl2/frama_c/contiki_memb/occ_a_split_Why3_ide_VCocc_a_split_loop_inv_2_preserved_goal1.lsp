;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/occ_a_split_Why3_ide_VCocc_a_split_loop_inv_2_preserved_goal1:
;; preservation of an occurrence-count interval split when the upper endpoint
;; advances by one, under the stated ordering, memory-region, constancy, and
;; signed-32-bit hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun oas1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun oas1-address-base (address)
  (car address))

(defun oas1-address-offset (address)
  (cdr address))

(defun oas1-shift (address amount)
  (cons
   (oas1-address-base address)
   (+ (oas1-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t, region function, and sconst predicate at t.

(defstub oas1-t (address) t)
(defstub oas1-region (base) t)
(defstub oas1-sconst-op () t)

(defun-sk oas1-function-types-p ()
  (forall (address base)
    (and
     (implies
      (oas1-address-p address)
      (integerp (oas1-t address)))
     (implies
      (integerp base)
      (integerp (oas1-region base))))))

(defun oas1-sconst-p ()
  (if (oas1-sconst-op) t nil))

(defun oas1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; The source l_occ_a function is uniquely characterized by zero on empty
;; intervals and a one-step recurrence at the right endpoint. This terminating
;; recursion is the corresponding exact finite occurrence count.

(defun oas1-occ-aux (element array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (oas1-t
           (oas1-shift array (+ from (1- remaining))))
          element)
         1
       0)
     (oas1-occ-aux element array from (1- remaining)))))

(defun oas1-occ (element array from to)
  (if
      (and
       (integerp element)
       (oas1-address-p array)
       (integerp from)
       (integerp to)
       (< from to))
      (oas1-occ-aux element array from (- to from))
    0))

(defun-sk
    ntp4vc-occ-a-split-loop-inv-2-preserved-goal1-statement ()
  (forall
   (i3 a i2 i4 i1 i)
   (implies
    (and
     (oas1-function-types-p)
     (integerp i3)
     (oas1-address-p a)
     (integerp i2)
     (integerp i4)
     (integerp i1)
     (integerp i))
    (let*
        ((x (oas1-occ i3 a i2 i4))
         (x1 (+ 1 i1)))
      (implies
       (and
        (equal
         (+ x (oas1-occ i3 a i4 i1))
         (oas1-occ i3 a i2 i1))
        (<= i1 i)
        (<= i4 i)
        (< i1 i)
        (<= i4 i1)
        (<= i2 i4)
        (<= (oas1-region (oas1-address-base a)) 0)
        (<= i1 2147483646)
        (oas1-sconst-p)
        (oas1-is-sint32-p i)
        (oas1-is-sint32-p i1)
        (oas1-is-sint32-p i2)
        (oas1-is-sint32-p i3)
        (oas1-is-sint32-p i4)
        (oas1-is-sint32-p x1))
       (equal
        (+ x (oas1-occ i3 a i4 x1))
        (oas1-occ i3 a i2 x1)))))))

(value-triple :itpeval-statement-checked)

:q
