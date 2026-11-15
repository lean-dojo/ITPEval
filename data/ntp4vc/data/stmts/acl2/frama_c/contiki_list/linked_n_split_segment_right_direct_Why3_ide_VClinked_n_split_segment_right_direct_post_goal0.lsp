;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_right_direct_Why3_ide_VClinked_n_split_segment_right_direct_post_goal0:
;; direct splitting of an inductively defined linked-list segment at its right
;; end, with the shortened prefix ending at the derived next pointer. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssrdg0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssrdg0-address-base (address)
  (car address))

(defun lnssrdg0-address-offset (address)
  (cdr address))

(defun lnssrdg0-shift (address amount)
  (cons
   (lnssrdg0-address-base address)
   (+ (lnssrdg0-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssrdg0-t1 (address) t)
(defstub lnssrdg0-t (index) t)
(defstub lnssrdg0-region (base) t)
(defstub lnssrdg0-linked-op () t)

(defun-sk lnssrdg0-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssrdg0-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssrdg0-address-p (lnssrdg0-t1 address))
      (integerp (lnssrdg0-t index))
      (integerp (lnssrdg0-region base))))))

(defun lnssrdg0-linked-p ()
  (if (lnssrdg0-linked-op) t nil))

(defun lnssrdg0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssrdg0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssrdg0-address-base address))
    (<= 0 (lnssrdg0-address-offset address))
    (<=
     (+ (lnssrdg0-address-offset address) length)
     (lnssrdg0-t (lnssrdg0-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssrdg0-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssrdg0-address-p root)
   (lnssrdg0-address-p array)
   (integerp index)
   (integerp n)
   (lnssrdg0-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssrdg0-t1 (lnssrdg0-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssrdg0-valid-rw-p root 4)
      (lnssrdg0-p-linked-n-p
       (lnssrdg0-t1 (lnssrdg0-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssrdg0-framed-p ()
  (forall (address)
    (implies
     (lnssrdg0-address-p address)
     (<=
      (lnssrdg0-region
       (lnssrdg0-address-base (lnssrdg0-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-right-direct-post-goal0-statement ()
  (forall
   (a2 i i1 a a1)
   (implies
    (and
     (lnssrdg0-function-types-p)
     (lnssrdg0-address-p a2)
     (integerp i)
     (integerp i1)
     (lnssrdg0-address-p a)
     (lnssrdg0-address-p a1))
    (let
        ((a3
          (lnssrdg0-t1
           (lnssrdg0-shift
            (lnssrdg0-t1
             (lnssrdg0-shift a2 (- (+ i i1) 1)))
            0))))
      (implies
       (and
        (< 0 i)
        (<= (lnssrdg0-region (lnssrdg0-address-base a)) 0)
        (<= (lnssrdg0-region (lnssrdg0-address-base a1)) 0)
        (<= (lnssrdg0-region (lnssrdg0-address-base a2)) 0)
        (<= (lnssrdg0-region (lnssrdg0-address-base a3)) 0)
        (lnssrdg0-framed-p)
        (lnssrdg0-linked-p)
        (lnssrdg0-is-sint32-p i)
        (lnssrdg0-is-sint32-p i1)
        (lnssrdg0-valid-rw-p
         (lnssrdg0-shift a2 0)
         2147483646)
        (lnssrdg0-p-linked-n-p
         a a2 i1 (+ 1 i) a1))
       (lnssrdg0-p-linked-n-p
        a a2 i1 i a3))))))

(value-triple :itpeval-statement-checked)

:q
