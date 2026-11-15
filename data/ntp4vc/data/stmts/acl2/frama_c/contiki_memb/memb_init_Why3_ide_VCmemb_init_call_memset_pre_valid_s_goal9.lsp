;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_call_memset_pre_valid_s_goal9:
;; validity or emptiness of the memb count block under the stated framing,
;; memory-validity, memb-structure, and unsigned-integer hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mi9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mi9-address-base (address)
  (car address))

(defun mi9-address-offset (address)
  (cdr address))

(defun mi9-shift (address amount)
  (cons
   (mi9-address-base address)
   (+ (mi9-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, region
;; function, and the fixed linked and sconst predicates at those functions.

(defstub mi9-t3 (address) t)
(defstub mi9-t1 (address) t)
(defstub mi9-t2 (address) t)
(defstub mi9-malloc (index) t)
(defstub mi9-region (base) t)
(defstub mi9-linked-op () t)
(defstub mi9-sconst-op () t)

(defun-sk mi9-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mi9-address-p address)
      (and
       (mi9-address-p (mi9-t3 address))
       (integerp (mi9-t1 address))
       (integerp (mi9-t2 address))))
     (implies
      (integerp index)
      (integerp (mi9-malloc index)))
     (implies
      (integerp base)
      (integerp (mi9-region base))))))

(defun mi9-linked-p ()
  (if (mi9-linked-op) t nil))

(defun mi9-sconst-p ()
  (if (mi9-sconst-op) t nil))

(defun mi9-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun mi9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mi9-address-base address))
    (<= 0 (mi9-address-offset address))
    (<=
     (+ (mi9-address-offset address) length)
     (mi9-malloc (mi9-address-base address))))))

(defun mi9-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mi9-address-base address)))
    (<= 0 (mi9-address-offset address))
    (<=
     (+ (mi9-address-offset address) length)
     (mi9-malloc (mi9-address-base address))))))

(defun mi9-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mi9-address-base left)
     (mi9-address-base right)))
   (<=
    (+ (mi9-address-offset right) right-length)
    (mi9-address-offset left))
   (<=
    (+ (mi9-address-offset left) left-length)
    (mi9-address-offset right))))

(defun-sk mi9-framed-p ()
  (forall (address)
    (implies
     (mi9-address-p address)
     (<=
      (mi9-region
       (mi9-address-base (mi9-t3 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun mi9-p-valid-memb-p (m)
  (let*
      ((element-size
        (mi9-t1 (mi9-shift m 0)))
       (element-count
        (mi9-t1 (mi9-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mi9-t3 (mi9-shift m 2)))
       (payload-array
        (mi9-t3 (mi9-shift m 3)))
       (count-start (mi9-shift count-array 0))
       (payload-start (mi9-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mi9-valid-rw-p m 4)
     (mi9-valid-rw-p count-array 1)
     (mi9-valid-rw-p payload-array 1)
     (mi9-valid-rw-p count-start element-count)
     (mi9-valid-rw-p payload-start payload-size)
     (mi9-separated-p
      count-start element-count payload-start payload-size))))

;; By base_offset_zero and base_offset_inj, the source condition
;; base_offset(offset(s)) = 0 is equivalent to offset(s) = 0.

(defun mi9-empty-block-p (address)
  (and
   (equal
    (mi9-malloc (mi9-address-base address))
    0)
   (equal (mi9-address-offset address) 0)))

(defun mi9-valid-or-empty-p (address length)
  (and
   (mi9-valid-rw-p (mi9-shift address 0) length)
   (or
    (mi9-empty-block-p address)
    (mi9-valid-rd-p address 1))))

(defun-sk
    ntp4vc-memb-init-call-memset-pre-valid-s-goal9-statement ()
  (forall
   (a)
   (implies
    (and
     (mi9-function-types-p)
     (mi9-address-p a))
    (let*
        ((a1 (mi9-shift a 1))
         (x (mi9-t1 a1))
         (a2 (mi9-shift a 2)))
      (implies
       (and
        (<= (mi9-region (mi9-address-base a)) 0)
        (mi9-framed-p)
        (mi9-linked-p)
        (mi9-sconst-p)
        (mi9-is-uint16-p x)
        (mi9-is-uint16-p
         (mi9-t1 (mi9-shift a 0)))
        (mi9-p-valid-memb-p a)
        (mi9-valid-rd-p a2 1)
        (mi9-valid-rd-p a1 1))
       (mi9-valid-or-empty-p
        (mi9-t3 a2)
        x))))))

(value-triple :itpeval-statement-checked)

:q
