;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_4_established_goal11:
;; establishment of the linked-list segment start invariant while merging two
;; adjacent segments. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnmsg11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnmsg11-address-base (address)
  (car address))

(defun lnmsg11-address-offset (address)
  (cdr address))

(defun lnmsg11-shift (address amount)
  (cons
   (lnmsg11-address-base address)
   (+ (lnmsg11-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnmsg11-t1 (address) t)
(defstub lnmsg11-t (index) t)
(defstub lnmsg11-region (base) t)
(defstub lnmsg11-linked-op () t)

(defun-sk lnmsg11-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnmsg11-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnmsg11-address-p (lnmsg11-t1 address))
      (integerp (lnmsg11-t index))
      (integerp (lnmsg11-region base))))))

(defun lnmsg11-linked-p ()
  (if (lnmsg11-linked-op) t nil))

(defun lnmsg11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnmsg11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnmsg11-address-base address))
    (<= 0 (lnmsg11-address-offset address))
    (<=
     (+ (lnmsg11-address-offset address) length)
     (lnmsg11-t (lnmsg11-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnmsg11-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnmsg11-address-p root)
   (lnmsg11-address-p array)
   (integerp index)
   (integerp n)
   (lnmsg11-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnmsg11-t1 (lnmsg11-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnmsg11-valid-rw-p root 4)
      (lnmsg11-p-linked-n-p
       (lnmsg11-t1 (lnmsg11-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnmsg11-framed-p ()
  (forall (address)
    (implies
     (lnmsg11-address-p address)
     (<=
      (lnmsg11-region
       (lnmsg11-address-base (lnmsg11-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-merge-segment-loop-inv-4-established-goal11-statement ()
  (forall
   (i1 i2 i a a1 a2 a3)
   (implies
    (and
     (lnmsg11-function-types-p)
     (integerp i1)
     (integerp i2)
     (integerp i)
     (lnmsg11-address-p a)
     (lnmsg11-address-p a1)
     (lnmsg11-address-p a2)
     (lnmsg11-address-p a3))
    (implies
     (and
      (not (equal i2 0))
      (<= 0 i)
      (<= 0 i2)
      (<= (lnmsg11-region (lnmsg11-address-base a)) 0)
      (<= (lnmsg11-region (lnmsg11-address-base a1)) 0)
      (<= (lnmsg11-region (lnmsg11-address-base a2)) 0)
      (<= (lnmsg11-region (lnmsg11-address-base a3)) 0)
      (lnmsg11-framed-p)
      (lnmsg11-linked-p)
      (lnmsg11-is-sint32-p i)
      (lnmsg11-is-sint32-p i1)
      (lnmsg11-is-sint32-p i2)
      (lnmsg11-valid-rw-p
       (lnmsg11-shift a3 0)
       2147483646)
      (lnmsg11-p-linked-n-p
       a a3 i1 i2 a2)
      (lnmsg11-p-linked-n-p
       a2 a3 (+ i1 i2) i a1))
     (lnmsg11-p-linked-n-p
      (lnmsg11-t1
       (lnmsg11-shift
        (lnmsg11-t1
         (lnmsg11-shift a3 (- (+ i1 i2) 1)))
        0))
      a3
      (+ i1 i2)
      i
      a1)))))

(value-triple :itpeval-statement-checked)

:q
