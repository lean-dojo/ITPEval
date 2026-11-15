;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_post_2_goal0:
;; preservation of the idle-core property for a CPU mask after cpumask-andnot,
;; under the stated memory validity, framing, separation, havoc-agreement, and
;; quantified loop-invariant hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun cpp20-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun cpp20-address-base (address)
  (car address))

(defun cpp20-address-offset (address)
  (cdr address))

(defun cpp20-shift (address amount)
  (cons
   (cpp20-address-base address)
   (+ (cpp20-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, and the
;; fixed region, CPU-mask, idle-CPU, linked, and l_size symbols.

(defstub cpp20-t3 (address) t)
(defstub cpp20-t1 (address) t)
(defstub cpp20-t2 (address) t)
(defstub cpp20-allocation (index) t)
(defstub cpp20-region (base) t)
(defstub cpp20-l-cpu-smt-mask (index) t)
(defstub cpp20-l-idle-cpu (index) t)
(defstub cpp20-linked-op () t)
(defstub cpp20-l-size () t)
(defstub cpp20-mask-memory-apply (memory-symbol address) t)
(defstub cpp20-mask-pointer-apply (pointer-symbol address) t)

(defun cpp20-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk cpp20-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (cpp20-address-p address)
      (and
       (integerp
        (cpp20-mask-memory-apply
         memory-symbol address))
       (cpp20-address-p
        (cpp20-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (cpp20-is-uint8-p
        (cpp20-l-idle-cpu index))
       (cpp20-address-p
        (cpp20-l-cpu-smt-mask index)))))))

(defun-sk cpp20-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (cpp20-address-p address)
     (equal
      (cpp20-mask-memory-apply
       'cpp20-zero-memory address)
      0))))

(defun-sk cpp20-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (cpp20-l-size)))
     (not
      (equal
       (cpp20-mask-memory-apply
        memory-symbol
        (cpp20-shift
         (cpp20-mask-pointer-apply
          pointer-symbol
          (cpp20-shift
           (cpp20-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk cpp20-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (cpp20-mask-memory-apply
         memory-symbol
         (cpp20-shift
          (cpp20-mask-pointer-apply
           pointer-symbol
           (cpp20-shift
            (cpp20-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (cpp20-l-size))
      (<= 0 j)
      (< j (cpp20-l-size)))
     (not
      (equal
       (cpp20-mask-memory-apply
        memory-symbol
        (cpp20-shift
         (cpp20-mask-pointer-apply
          pointer-symbol
          (cpp20-shift
           (cpp20-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk cpp20-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (cpp20-mask-memory-apply
         memory-symbol
         (cpp20-shift
          (cpp20-mask-pointer-apply
           pointer-symbol
           (cpp20-shift
            (cpp20-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (cpp20-mask-memory-apply
         memory-symbol
         (cpp20-shift
          (cpp20-mask-pointer-apply
           pointer-symbol
           (cpp20-shift
            (cpp20-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (cpp20-l-size))
      (<= 0 j)
      (< j (cpp20-l-size))
      (<= 0 k)
      (< k (cpp20-l-size)))
     (not
      (equal
       (cpp20-mask-memory-apply
        memory-symbol
        (cpp20-shift
         (cpp20-mask-pointer-apply
          pointer-symbol
          (cpp20-shift
           (cpp20-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun-sk cpp20-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (cpp20-address-p address)
      (and
       (cpp20-address-p (cpp20-t3 address))
       (integerp (cpp20-t1 address))
       (integerp (cpp20-t2 address))))
     (implies
      (integerp index)
      (and
       (integerp (cpp20-allocation index))
       (cpp20-address-p (cpp20-l-cpu-smt-mask index))
       (cpp20-is-uint8-p (cpp20-l-idle-cpu index))))
     (implies
      (integerp base)
      (integerp (cpp20-region base))))))

(defun cpp20-linked-p ()
  (if (cpp20-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32), the mathematical
;; unsigned 32-bit conversion on every source integer.

(defun cpp20-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun cpp20-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun cpp20-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (cpp20-address-base address))
    (<= 0 (cpp20-address-offset address))
    (<=
     (+ (cpp20-address-offset address) length)
     (cpp20-allocation (cpp20-address-base address))))))

(defun cpp20-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (cpp20-address-base address)))
    (<= 0 (cpp20-address-offset address))
    (<=
     (+ (cpp20-address-offset address) length)
     (cpp20-allocation (cpp20-address-base address))))))

(defun cpp20-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (cpp20-address-base left)
     (cpp20-address-base right)))
   (<=
    (+ (cpp20-address-offset right) right-length)
    (cpp20-address-offset left))
   (<=
    (+ (cpp20-address-offset left) left-length)
    (cpp20-address-offset right))))

;; Exact unfolding of Memory.framed for the arbitrary pointer memory t_3.

(defun-sk cpp20-framed-p ()
  (forall (address)
    (implies
     (cpp20-address-p address)
     (<=
      (cpp20-region
       (cpp20-address-base (cpp20-t3 address)))
      0))))

;; This is the exact havoc_access value for
;; havoc t_1 t_2 protected-start protected-length at query.

(defun cpp20-havoc-value
    (protected-start protected-length query)
  (if
      (cpp20-separated-p
       query 1 protected-start protected-length)
      (cpp20-t2 query)
    (cpp20-t1 query)))

;; Exact specializations of p_idle_core to the havoced memory a_9 and to t_2.

(defun-sk cpp20-havoc-idle-core-p
    (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (cpp20-havoc-value
         protected-start
         (cpp20-l-size)
         (cpp20-shift
          (cpp20-t3
           (cpp20-shift
            (cpp20-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (cpp20-l-size))
        (not (equal (cpp20-l-idle-cpu index) 0))))))))

(defun-sk cpp20-t2-idle-core-p (cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (cpp20-t2
         (cpp20-shift
          (cpp20-t3
           (cpp20-shift
            (cpp20-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (cpp20-l-size))
        (not (equal (cpp20-l-idle-cpu index) 0))))))))

;; Preserve the source universal separation condition for every integer i_2
;; in [0, l_size).

(defun-sk cpp20-mask-separated-p (a8)
  (forall (i2)
    (implies
     (integerp i2)
     (implies
      (<= 0 i2)
      (implies
       (< i2 (cpp20-l-size))
       (cpp20-separated-p
        a8
        (cpp20-l-size)
        (cpp20-shift
         (cpp20-t3
          (cpp20-shift (cpp20-l-cpu-smt-mask i2) 0))
         0)
        (cpp20-l-size)))))))

;; Preserve the source universal agreement between the havoced memory and t_2
;; from the current index through the end of the mask.

(defun-sk cpp20-tail-havoc-agreement-p (a7 a8 i)
  (forall (i2)
    (implies
     (integerp i2)
     (implies
      (<= i i2)
      (implies
       (< i2 (cpp20-l-size))
       (let ((a10 (cpp20-shift a7 i2)))
         (iff
          (not
           (equal
            (cpp20-havoc-value
             a8
             (cpp20-l-size)
             a10)
            0))
          (not (equal (cpp20-t2 a10) 0)))))))))

;; Preserve the source universal loop invariant over every earlier integer
;; index i_2.

(defun-sk cpp20-prefix-invariant-p (a3 a5 a7 a8 i)
  (forall (i2)
    (implies
     (integerp i2)
     (implies
      (<= 0 i2)
      (implies
       (< i2 i)
       (iff
        (and
         (equal (cpp20-t2 (cpp20-shift a3 i2)) 0)
         (not
          (equal
           (cpp20-t2 (cpp20-shift a5 i2))
           0)))
        (not
         (equal
          (cpp20-havoc-value
           a8
           (cpp20-l-size)
           (cpp20-shift a7 i2))
          0))))))))

(defun-sk
    ntp4vc-cpumask-andnot-post-2-goal0-statement ()
  (forall
   (a a1 a2 i i1)
   (implies
    (and
     (cpp20-function-types-p)
     (cpp20-scheduler-schema-types-p)
     (cpp20-zero-mask-memory-instance-p)
     (cpp20-q-mask-refl-p)
     (cpp20-q-mask-symm-p)
     (cpp20-q-mask-trans-p)
     (integerp (cpp20-l-size))
     (< 0 (cpp20-l-size))
     (<= (cpp20-l-size) 2147483647)
     (cpp20-address-p a)
     (cpp20-address-p a1)
     (cpp20-address-p a2)
     (integerp i)
     (integerp i1))
    (let*
        ((a3 (cpp20-t3 (cpp20-shift a 0)))
         (a4 (cpp20-shift a3 0))
         (a5 (cpp20-t3 (cpp20-shift a1 0)))
         (a6 (cpp20-shift a5 0))
         (a7 (cpp20-t3 (cpp20-shift a2 0)))
         (a8 (cpp20-shift a7 0)))
      (implies
       (and
        (not (equal (cons 0 0) a2))
        (equal
         (cpp20-to-uint32 i)
         (cpp20-l-size))
        (<= 0 i)
        (<= 0 i1)
        (< i1 (cpp20-l-size))
        (<= i (cpp20-l-size))
        (<= (cpp20-region (cpp20-address-base a)) 0)
        (<= (cpp20-region (cpp20-address-base a1)) 0)
        (<= (cpp20-region (cpp20-address-base a2)) 0)
        (cpp20-framed-p)
        (cpp20-linked-p)
        (cpp20-is-sint32-p i)
        (cpp20-valid-rd-p a 1)
        (cpp20-valid-rd-p a1 1)
        (cpp20-valid-rd-p a2 1)
        (cpp20-valid-rd-p a4 (cpp20-l-size))
        (cpp20-valid-rd-p a6 (cpp20-l-size))
        (cpp20-valid-rw-p a8 (cpp20-l-size))
        (cpp20-havoc-idle-core-p a8 i1)
        (implies
         (not (equal a2 a))
         (cpp20-separated-p
          a8 (cpp20-l-size) a4 (cpp20-l-size)))
        (implies
         (not (equal a2 a1))
         (cpp20-separated-p
          a8 (cpp20-l-size) a6 (cpp20-l-size)))
        (cpp20-mask-separated-p a8)
        (cpp20-tail-havoc-agreement-p a7 a8 i)
        (cpp20-prefix-invariant-p a3 a5 a7 a8 i))
       (cpp20-t2-idle-core-p i1))))))

(value-triple :itpeval-statement-checked)

:q
