;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_assert_rte_signed_overflow_2_goal6:
;; the signed 32-bit upper-bound safety obligation for the product of the
;; memb element count and element size under the stated framing, memory
;; validity, range, and zero-initialization hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mi6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mi6-address-base (address)
  (car address))

(defun mi6-address-offset (address)
  (cdr address))

(defun mi6-shift (address amount)
  (cons
   (mi6-address-base address)
   (+ (mi6-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_4, integer memories t_1, t_3, and t_2, allocation map t,
;; and the fixed region, linked, and sconst operations at those functions.

(defstub mi6-t4 (address) t)
(defstub mi6-t1 (address) t)
(defstub mi6-t3 (address) t)
(defstub mi6-t2 (address) t)
(defstub mi6-malloc (index) t)
(defstub mi6-region (base) t)
(defstub mi6-linked-op () t)
(defstub mi6-sconst-op () t)

(defun-sk mi6-function-types-p ()
  (forall (address index)
    (and
     (implies
      (mi6-address-p address)
      (and
       (mi6-address-p (mi6-t4 address))
       (integerp (mi6-t1 address))
       (integerp (mi6-t3 address))
       (integerp (mi6-t2 address))))
     (implies
      (integerp index)
      (and
       (integerp (mi6-malloc index))
       (integerp (mi6-region index)))))))

(defun mi6-linked-p ()
  (if (mi6-linked-op) t nil))

(defun mi6-sconst-p ()
  (if (mi6-sconst-op) t nil))

(defun mi6-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun mi6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mi6-address-base address))
    (<= 0 (mi6-address-offset address))
    (<=
     (+ (mi6-address-offset address) length)
     (mi6-malloc (mi6-address-base address))))))

(defun mi6-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mi6-address-base address)))
    (<= 0 (mi6-address-offset address))
    (<=
     (+ (mi6-address-offset address) length)
     (mi6-malloc (mi6-address-base address))))))

(defun mi6-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mi6-address-base left)
     (mi6-address-base right)))
   (<=
    (+ (mi6-address-offset right) right-length)
    (mi6-address-offset left))
   (<=
    (+ (mi6-address-offset left) left-length)
    (mi6-address-offset right))))

(defun-sk mi6-framed-p ()
  (forall (address)
    (implies
     (mi6-address-p address)
     (<=
      (mi6-region
       (mi6-address-base (mi6-t4 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun mi6-p-valid-memb-p (m)
  (let*
      ((element-size
        (mi6-t1 (mi6-shift m 0)))
       (element-count
        (mi6-t1 (mi6-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mi6-t4 (mi6-shift m 2)))
       (payload-array
        (mi6-t4 (mi6-shift m 3)))
       (count-start (mi6-shift count-array 0))
       (payload-start (mi6-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mi6-valid-rw-p m 4)
     (mi6-valid-rw-p count-array 1)
     (mi6-valid-rw-p payload-array 1)
     (mi6-valid-rw-p count-start element-count)
     (mi6-valid-rw-p payload-start payload-size)
     (mi6-separated-p
      count-start element-count payload-start payload-size))))

;; By base_offset_zero and base_offset_inj, the source condition
;; base_offset(offset(s)) = 0 is equivalent to offset(s) = 0.

(defun mi6-empty-block-p (address)
  (and
   (equal
    (mi6-malloc (mi6-address-base address))
    0)
   (equal (mi6-address-offset address) 0)))

(defun mi6-valid-or-empty-p (address length)
  (and
   (mi6-valid-rw-p (mi6-shift address 0) length)
   (or
    (mi6-empty-block-p address)
    (mi6-valid-rd-p address 1))))

;; This is the exact havoc_access value for
;; havoc t_2 t_3 protected-start protected-length at query.

(defun mi6-havoc-value
    (protected-start protected-length query)
  (if
      (mi6-separated-p
       query 1 protected-start protected-length)
      (mi6-t3 query)
    (mi6-t2 query)))

;; Q_memset_def and havoc_access make the source l_memset hypothesis
;; equivalent to this universal condition over every mathematical integer.

(defun-sk mi6-memset-havoc-zero-p (start length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index length))
     (equal
      (mi6-havoc-value
       (mi6-shift start 0)
       length
       (mi6-shift start index))
      0))))

(defun-sk
    ntp4vc-memb-init-assert-rte-signed-overflow-2-goal6-statement ()
  (forall
   (a)
   (implies
    (and
     (mi6-function-types-p)
     (mi6-address-p a))
    (let*
        ((a1 (mi6-shift a 1))
         (x (mi6-t1 a1))
         (x1 (mi6-t1 (mi6-shift a 0)))
         (a2 (mi6-shift a 2))
         (a3 (mi6-t4 a2)))
      (implies
       (and
        (<= (mi6-region (mi6-address-base a)) 0)
        (mi6-framed-p)
        (mi6-linked-p)
        (mi6-sconst-p)
        (mi6-is-uint16-p x)
        (mi6-is-uint16-p x1)
        (mi6-p-valid-memb-p a)
        (mi6-valid-rd-p a2 1)
        (mi6-valid-rd-p a1 1)
        (mi6-valid-or-empty-p a3 x)
        (mi6-memset-havoc-zero-p a3 x))
       (<= (* x x1) 2147483647))))))

(value-triple :itpeval-statement-checked)

:q
