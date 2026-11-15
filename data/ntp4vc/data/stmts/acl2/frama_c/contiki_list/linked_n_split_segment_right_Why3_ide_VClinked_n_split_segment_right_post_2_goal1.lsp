;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_right_Why3_ide_VClinked_n_split_segment_right_post_2_goal1:
;; extraction of the rightmost one-node suffix of an inductively defined
;; linked-list segment. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssrg1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssrg1-address-base (address)
  (car address))

(defun lnssrg1-address-offset (address)
  (cdr address))

(defun lnssrg1-shift (address amount)
  (cons
   (lnssrg1-address-base address)
   (+ (lnssrg1-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssrg1-t1 (address) t)
(defstub lnssrg1-t (index) t)
(defstub lnssrg1-region (base) t)
(defstub lnssrg1-linked-op () t)

(defun-sk lnssrg1-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssrg1-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssrg1-address-p (lnssrg1-t1 address))
      (integerp (lnssrg1-t index))
      (integerp (lnssrg1-region base))))))

(defun lnssrg1-linked-p ()
  (if (lnssrg1-linked-op) t nil))

(defun lnssrg1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssrg1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssrg1-address-base address))
    (<= 0 (lnssrg1-address-offset address))
    (<=
     (+ (lnssrg1-address-offset address) length)
     (lnssrg1-t (lnssrg1-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssrg1-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssrg1-address-p root)
   (lnssrg1-address-p array)
   (integerp index)
   (integerp n)
   (lnssrg1-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssrg1-t1 (lnssrg1-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssrg1-valid-rw-p root 4)
      (lnssrg1-p-linked-n-p
       (lnssrg1-t1 (lnssrg1-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssrg1-framed-p ()
  (forall (address)
    (implies
     (lnssrg1-address-p address)
     (<=
      (lnssrg1-region
       (lnssrg1-address-base (lnssrg1-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-right-post-2-goal1-statement ()
  (forall
   (a2 i i1 a a1)
   (implies
    (and
     (lnssrg1-function-types-p)
     (lnssrg1-address-p a2)
     (integerp i)
     (integerp i1)
     (lnssrg1-address-p a)
     (lnssrg1-address-p a1))
    (let
        ((a3
          (lnssrg1-t1
           (lnssrg1-shift
            (lnssrg1-t1
             (lnssrg1-shift a2 (- (+ i i1) 1)))
            0))))
      (implies
       (and
        (< 0 i)
        (<= (lnssrg1-region (lnssrg1-address-base a)) 0)
        (<= (lnssrg1-region (lnssrg1-address-base a1)) 0)
        (<= (lnssrg1-region (lnssrg1-address-base a2)) 0)
        (<= (lnssrg1-region (lnssrg1-address-base a3)) 0)
        (lnssrg1-framed-p)
        (lnssrg1-linked-p)
        (lnssrg1-is-sint32-p i)
        (lnssrg1-is-sint32-p i1)
        (lnssrg1-valid-rw-p
         (lnssrg1-shift a2 0)
         2147483646)
        (lnssrg1-p-linked-n-p
         a a2 i1 (+ 1 i) a1))
       (lnssrg1-p-linked-n-p
        a3 a2 (+ i i1) 1 a1))))))

(value-triple :itpeval-statement-checked)

:q
