;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/strndup_Why3_ide_VCstrndup_call_memcpy_pre_4_goal5:
;; writable-memory validity for the source prefix length used by memcpy,
;; under the stated non-null, integer-range, allocation, linkedness,
;; constancy, and null-character prefix hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snd5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snd5-address-base (address)
  (car address))

(defun snd5-address-offset (address)
  (cdr address))

(defun snd5-shift (address amount)
  (cons
   (snd5-address-base address)
   (+ (snd5-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t, integer memory t_1, uint32 conversion, region function,
;; and the linked and sconst predicates specialized respectively to t and t_1.

(defstub snd5-allocation (index) t)
(defstub snd5-memory (address) t)
(defstub snd5-to-uint32 (value) t)
(defstub snd5-region (base) t)
(defstub snd5-linked-op () t)
(defstub snd5-sconst-op () t)

(defun-sk snd5-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (snd5-address-p address)
      (integerp (snd5-memory address)))
     (implies
      (integerp index)
      (integerp (snd5-allocation index)))
     (implies
      (integerp base)
      (integerp (snd5-region base)))
     (implies
      (integerp value)
      (integerp (snd5-to-uint32 value))))))

(defun snd5-linked-p ()
  (if (snd5-linked-op) t nil))

(defun snd5-sconst-p ()
  (if (snd5-sconst-op) t nil))

(defun snd5-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; These are exactly the imported Cint laws is_to_uint32, id_uint32, and
;; proj_uint32 for the arbitrary conversion function.

(defun-sk snd5-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snd5-is-uint32-p (snd5-to-uint32 value))
      (implies
       (snd5-is-uint32-p value)
       (equal (snd5-to-uint32 value) value))
      (equal
       (snd5-to-uint32 (snd5-to-uint32 value))
       (snd5-to-uint32 value))))))

;; Exact unfolding of Memory.valid_rw.

(defun snd5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (snd5-address-base address))
    (<= 0 (snd5-address-offset address))
    (<=
     (+ (snd5-address-offset address) length)
     (snd5-allocation (snd5-address-base address))))))

;; Exact universal and existential source conditions for null characters at
;; mathematical-integer offsets in [0, limit).

(defun-sk snd5-no-null-before-p (string limit)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position limit)
       (not
        (equal
         (snd5-memory
          (snd5-shift string position))
         0)))))))

(defun-sk snd5-null-in-prefix-p (string limit)
  (exists (position)
    (and
     (integerp position)
     (equal
      (snd5-memory
       (snd5-shift string position))
      0)
     (<= 0 position)
     (< position limit))))

(defun-sk ntp4vc-strndup-call-memcpy-pre-4-goal5-statement ()
  (forall
   (i1 a a1 i)
   (implies
    (and
     (integerp i1)
     (snd5-address-p a)
     (snd5-address-p a1)
     (integerp i)
     (snd5-function-types-p)
     (snd5-to-uint32-laws-p))
    (let*
        ((x (snd5-to-uint32 (+ 1 i1)))
         (a2 (snd5-shift a 0)))
      (implies
       (and
        (not (equal (cons 0 0) a1))
        (not (equal x 0))
        (<= 0 i)
        (<= (snd5-region (snd5-address-base a)) 0)
        (snd5-linked-p)
        (snd5-sconst-p)
        (snd5-is-uint32-p i)
        (snd5-is-uint32-p i1)
        (snd5-valid-rw-p a2 i)
        (implies
         (< 0 x)
         (snd5-valid-rw-p (snd5-shift a1 0) x))
        (implies
         (snd5-no-null-before-p a i)
         (equal i1 i))
        (implies
         (snd5-null-in-prefix-p a i)
         (<= i1 i)))
       (snd5-valid-rw-p a2 i1))))))

(value-triple :itpeval-statement-checked)

:q
