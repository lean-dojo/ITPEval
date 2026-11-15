;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sort/HeapMaximum_Why3_ide_VCHeapMaximum_loop_inv_2_preserved_goal2:
;; preservation of the heap-maximum loop invariant: the selected heap entry
;; is bounded by the root value under the stated index bounds, unsigned-32
;; conditions, heap property, region condition, and prefix bound.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun hmg2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun hmg2-address-base (address)
  (car address))

(defun hmg2-address-offset (address)
  (cdr address))

(defun hmg2-shift (address amount)
  (cons
   (hmg2-address-base address)
   (+ (hmg2-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memory t
;; and region function in the source statement.

(defstub hmg2-memory (address) t)
(defstub hmg2-region (base) t)

(defun-sk hmg2-function-types-p ()
  (forall (address base)
    (and
     (implies
      (hmg2-address-p address)
      (integerp (hmg2-memory address)))
     (implies
      (integerp base)
      (integerp (hmg2-region base))))))

(defun hmg2-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Exact unfolding of Axiomatic1.p_isheap. Its child index is positive, so
;; floor((child - 1)/2) is the source truncating quotient l_heapparent.

(defun-sk hmg2-isheap-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (hmg2-memory (hmg2-shift a child))
      (hmg2-memory
       (hmg2-shift a (floor (- child 1) 2)))))))

;; The source loop invariant remains universally quantified over every
;; mathematical integer index below i1.

(defun-sk hmg2-prefix-bounded-by-root-p (a i1)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index i1))
      (<=
       (hmg2-memory (hmg2-shift a index))
       (hmg2-memory (hmg2-shift a 0)))))))

(defun-sk
    ntp4vc-heap-maximum-loop-inv-2-preserved-goal2-statement ()
  (forall
   (a i i1 i2)
   (implies
    (and
     (hmg2-address-p a)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (hmg2-function-types-p))
    (let ((x (hmg2-memory (hmg2-shift a 0))))
      (implies
       (and
        (< 0 i)
        (<= i1 i)
        (<= 0 i1)
        (< i1 i)
        (<= i2 i1)
        (<= 0 i2)
        (<= (hmg2-region (hmg2-address-base a)) 0)
        (<= i1 4294967294)
        (hmg2-is-uint32-p i)
        (hmg2-is-uint32-p i1)
        (hmg2-is-uint32-p i2)
        (hmg2-isheap-p a i)
        (hmg2-is-uint32-p (+ 1 i1))
        (hmg2-prefix-bounded-by-root-p a i1))
       (<=
        (hmg2-memory (hmg2-shift a i2))
        x))))))

(value-triple :itpeval-statement-checked)

:q
