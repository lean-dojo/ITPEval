;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_merge_segment_right_Why3_ide_VClinked_n_merge_segment_right_post_goal0:
;; concatenation of adjacent inductively defined linked-list segments into a
;; segment whose length is increased by one. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnmsrg0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnmsrg0-address-base (address)
  (car address))

(defun lnmsrg0-address-offset (address)
  (cdr address))

(defun lnmsrg0-shift (address amount)
  (cons
   (lnmsrg0-address-base address)
   (+ (lnmsrg0-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnmsrg0-t1 (address) t)
(defstub lnmsrg0-t (index) t)
(defstub lnmsrg0-region (base) t)
(defstub lnmsrg0-linked-op () t)

(defun-sk lnmsrg0-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnmsrg0-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnmsrg0-address-p (lnmsrg0-t1 address))
      (integerp (lnmsrg0-t index))
      (integerp (lnmsrg0-region base))))))

(defun lnmsrg0-linked-p ()
  (if (lnmsrg0-linked-op) t nil))

(defun lnmsrg0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnmsrg0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnmsrg0-address-base address))
    (<= 0 (lnmsrg0-address-offset address))
    (<=
     (+ (lnmsrg0-address-offset address) length)
     (lnmsrg0-t (lnmsrg0-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnmsrg0-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnmsrg0-address-p root)
   (lnmsrg0-address-p array)
   (integerp index)
   (integerp n)
   (lnmsrg0-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnmsrg0-t1 (lnmsrg0-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnmsrg0-valid-rw-p root 4)
      (lnmsrg0-p-linked-n-p
       (lnmsrg0-t1 (lnmsrg0-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnmsrg0-framed-p ()
  (forall (address)
    (implies
     (lnmsrg0-address-p address)
     (<=
      (lnmsrg0-region
       (lnmsrg0-address-base (lnmsrg0-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-merge-segment-right-post-goal0-statement ()
  (forall
   (i a a1 a2 a3 i1)
   (implies
    (and
     (lnmsrg0-function-types-p)
     (integerp i)
     (lnmsrg0-address-p a)
     (lnmsrg0-address-p a1)
     (lnmsrg0-address-p a2)
     (lnmsrg0-address-p a3)
     (integerp i1))
    (implies
     (and
      (<= 0 i)
      (<= (lnmsrg0-region (lnmsrg0-address-base a)) 0)
      (<= (lnmsrg0-region (lnmsrg0-address-base a1)) 0)
      (<= (lnmsrg0-region (lnmsrg0-address-base a2)) 0)
      (<= (lnmsrg0-region (lnmsrg0-address-base a3)) 0)
      (lnmsrg0-framed-p)
      (lnmsrg0-linked-p)
      (lnmsrg0-is-sint32-p i)
      (lnmsrg0-is-sint32-p i1)
      (lnmsrg0-valid-rw-p
       (lnmsrg0-shift a3 0)
       2147483646)
      (lnmsrg0-p-linked-n-p
       a a3 i1 i a2)
      (lnmsrg0-p-linked-n-p
       a2 a3 (+ i i1) 1 a1))
     (lnmsrg0-p-linked-n-p
      a a3 i1 (+ 1 i) a1)))))

(value-triple :itpeval-statement-checked)

:q
