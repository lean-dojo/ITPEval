;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_call_memset_pre_valid_s_2_goal10:
;; validity or emptiness of the memb payload block after zero-initializing
;; the count block, under the stated framing, memory-validity, and integer
;; range hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mi10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mi10-address-base (address)
  (car address))

(defun mi10-address-offset (address)
  (cdr address))

(defun mi10-shift (address amount)
  (cons
   (mi10-address-base address)
   (+ (mi10-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_4, integer memories t_1, t_3, and t_2, allocation map t,
;; and the fixed region, linked, and sconst operations at those functions.

(defstub mi10-t4 (address) t)
(defstub mi10-t1 (address) t)
(defstub mi10-t3 (address) t)
(defstub mi10-t2 (address) t)
(defstub mi10-malloc (index) t)
(defstub mi10-region (base) t)
(defstub mi10-linked-op () t)
(defstub mi10-sconst-op () t)

(defun-sk mi10-function-types-p ()
  (forall (address index)
    (and
     (implies
      (mi10-address-p address)
      (and
       (mi10-address-p (mi10-t4 address))
       (integerp (mi10-t1 address))
       (integerp (mi10-t3 address))
       (integerp (mi10-t2 address))))
     (implies
      (integerp index)
      (and
       (integerp (mi10-malloc index))
       (integerp (mi10-region index)))))))

(defun mi10-linked-p ()
  (if (mi10-linked-op) t nil))

(defun mi10-sconst-p ()
  (if (mi10-sconst-op) t nil))

(defun mi10-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun mi10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mi10-address-base address))
    (<= 0 (mi10-address-offset address))
    (<=
     (+ (mi10-address-offset address) length)
     (mi10-malloc (mi10-address-base address))))))

(defun mi10-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mi10-address-base address)))
    (<= 0 (mi10-address-offset address))
    (<=
     (+ (mi10-address-offset address) length)
     (mi10-malloc (mi10-address-base address))))))

(defun mi10-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mi10-address-base left)
     (mi10-address-base right)))
   (<=
    (+ (mi10-address-offset right) right-length)
    (mi10-address-offset left))
   (<=
    (+ (mi10-address-offset left) left-length)
    (mi10-address-offset right))))

(defun-sk mi10-framed-p ()
  (forall (address)
    (implies
     (mi10-address-p address)
     (<=
      (mi10-region
       (mi10-address-base (mi10-t4 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun mi10-p-valid-memb-p (m)
  (let*
      ((element-size
        (mi10-t1 (mi10-shift m 0)))
       (element-count
        (mi10-t1 (mi10-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mi10-t4 (mi10-shift m 2)))
       (payload-array
        (mi10-t4 (mi10-shift m 3)))
       (count-start (mi10-shift count-array 0))
       (payload-start (mi10-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mi10-valid-rw-p m 4)
     (mi10-valid-rw-p count-array 1)
     (mi10-valid-rw-p payload-array 1)
     (mi10-valid-rw-p count-start element-count)
     (mi10-valid-rw-p payload-start payload-size)
     (mi10-separated-p
      count-start element-count payload-start payload-size))))

;; By base_offset_zero and base_offset_inj, the source condition
;; base_offset(offset(s)) = 0 is equivalent to offset(s) = 0.

(defun mi10-empty-block-p (address)
  (and
   (equal
    (mi10-malloc (mi10-address-base address))
    0)
   (equal (mi10-address-offset address) 0)))

(defun mi10-valid-or-empty-p (address length)
  (and
   (mi10-valid-rw-p (mi10-shift address 0) length)
   (or
    (mi10-empty-block-p address)
    (mi10-valid-rd-p address 1))))

;; This is the exact havoc_access value for
;; havoc t_2 t_3 protected-start protected-length at query.

(defun mi10-havoc-value
    (protected-start protected-length query)
  (if
      (mi10-separated-p
       query 1 protected-start protected-length)
      (mi10-t3 query)
    (mi10-t2 query)))

;; Q_memset_def and havoc_access make the source l_memset hypothesis
;; equivalent to this universal condition over every mathematical integer.

(defun-sk mi10-memset-havoc-zero-p (start length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index length))
     (equal
      (mi10-havoc-value
       (mi10-shift start 0)
       length
       (mi10-shift start index))
      0))))

;; Cint.to_uint32 is the canonical residue in [0, 2^32), which is the
;; mathematical unsigned 32-bit conversion on every source integer.

(defun mi10-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun-sk
    ntp4vc-memb-init-call-memset-pre-valid-s-2-goal10-statement ()
  (forall
   (a)
   (implies
    (and
     (mi10-function-types-p)
     (mi10-address-p a))
    (let*
        ((a1 (mi10-shift a 1))
         (x (mi10-t1 a1))
         (a2 (mi10-shift a 0))
         (x1 (mi10-t1 a2))
         (x2 (* x x1))
         (a3 (mi10-shift a 2))
         (a4 (mi10-shift a 3))
         (a5 (mi10-t4 a3)))
      (implies
       (and
        (<= (mi10-region (mi10-address-base a)) 0)
        (<= -2147483648 x2)
        (<= x2 2147483647)
        (mi10-framed-p)
        (mi10-linked-p)
        (mi10-sconst-p)
        (mi10-is-uint16-p x)
        (mi10-is-uint16-p x1)
        (mi10-p-valid-memb-p a)
        (mi10-valid-rd-p a3 1)
        (mi10-valid-rd-p a4 1)
        (mi10-valid-rd-p a1 1)
        (mi10-valid-rd-p a2 1)
        (mi10-valid-or-empty-p a5 x)
        (mi10-memset-havoc-zero-p a5 x))
       (mi10-valid-or-empty-p
        (mi10-t4 a4)
        (mi10-to-uint32 x2)))))))

(value-triple :itpeval-statement-checked)

:q
