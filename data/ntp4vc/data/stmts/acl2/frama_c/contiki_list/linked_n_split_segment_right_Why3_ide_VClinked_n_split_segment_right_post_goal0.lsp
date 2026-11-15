;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_right_Why3_ide_VClinked_n_split_segment_right_post_goal0:
;; splitting an inductively defined linked-list segment at its right end,
;; with the shortened prefix ending at the derived next pointer. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssrg0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssrg0-address-base (address)
  (car address))

(defun lnssrg0-address-offset (address)
  (cdr address))

(defun lnssrg0-shift (address amount)
  (cons
   (lnssrg0-address-base address)
   (+ (lnssrg0-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssrg0-t1 (address) t)
(defstub lnssrg0-t (index) t)
(defstub lnssrg0-region (base) t)
(defstub lnssrg0-linked-op () t)

(defun-sk lnssrg0-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssrg0-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssrg0-address-p (lnssrg0-t1 address))
      (integerp (lnssrg0-t index))
      (integerp (lnssrg0-region base))))))

(defun lnssrg0-linked-p ()
  (if (lnssrg0-linked-op) t nil))

(defun lnssrg0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssrg0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssrg0-address-base address))
    (<= 0 (lnssrg0-address-offset address))
    (<=
     (+ (lnssrg0-address-offset address) length)
     (lnssrg0-t (lnssrg0-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssrg0-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssrg0-address-p root)
   (lnssrg0-address-p array)
   (integerp index)
   (integerp n)
   (lnssrg0-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssrg0-t1 (lnssrg0-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssrg0-valid-rw-p root 4)
      (lnssrg0-p-linked-n-p
       (lnssrg0-t1 (lnssrg0-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssrg0-framed-p ()
  (forall (address)
    (implies
     (lnssrg0-address-p address)
     (<=
      (lnssrg0-region
       (lnssrg0-address-base (lnssrg0-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-right-post-goal0-statement ()
  (forall
   (a2 i i1 a a1)
   (implies
    (and
     (lnssrg0-function-types-p)
     (lnssrg0-address-p a2)
     (integerp i)
     (integerp i1)
     (lnssrg0-address-p a)
     (lnssrg0-address-p a1))
    (let
        ((a3
          (lnssrg0-t1
           (lnssrg0-shift
            (lnssrg0-t1
             (lnssrg0-shift a2 (- (+ i i1) 1)))
            0))))
      (implies
       (and
        (< 0 i)
        (<= (lnssrg0-region (lnssrg0-address-base a)) 0)
        (<= (lnssrg0-region (lnssrg0-address-base a1)) 0)
        (<= (lnssrg0-region (lnssrg0-address-base a2)) 0)
        (<= (lnssrg0-region (lnssrg0-address-base a3)) 0)
        (lnssrg0-framed-p)
        (lnssrg0-linked-p)
        (lnssrg0-is-sint32-p i)
        (lnssrg0-is-sint32-p i1)
        (lnssrg0-valid-rw-p
         (lnssrg0-shift a2 0)
         2147483646)
        (lnssrg0-p-linked-n-p
         a a2 i1 (+ 1 i) a1))
       (lnssrg0-p-linked-n-p
        a a2 i1 i a3))))))

(value-triple :itpeval-statement-checked)

:q
