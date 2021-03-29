; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

;; ---- Definitions ----

(defdata data (listof atom))

(defdata sender-state data)

(defdata receiver-state data)

;; Sim-state -- (sender-state receiver-state steps)
(defdata sim-state (list sender-state receiver-state nat))

(definec sim-state-ss (sim :sim-state) :sender-state
  (first sim))

(definec sim-state-rs (sim :sim-state) :receiver-state
  (second sim))

(definec sim-state-steps (sim :sim-state) :nat
  (third sim))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata sender-out (cons sender-state atom))

;; ---- Functions ----

(definec sender (sender-state :sender-state) :sender-out
  (cons (cdr sender-state) (car sender-state)))

(definec receiver (receiver-state :receiver-state packet :atom) :receiver-state
  (app receiver-state (list packet)))

(definec simulator-step (sim :sim-state) :sim-state
  :ic (posp (sim-state-steps sim))
  (let* ((ss-out (sender (sim-state-ss sim)))
	 (new-ss (car ss-out))
	 (packet (cdr ss-out))
	 (new-rs (receiver (sim-state-rs sim) packet)))
    (list new-ss new-rs (1- (sim-state-steps sim)))))

(definec simulator (sim :sim-state) :data
  (define (xargs :measure (sim-state-steps sim)
		 :termination-method :measure))
  :ic (>= (len (sim-state-ss sim)) (sim-state-steps sim))
  (cond
   ((zp (sim-state-steps sim)) (sim-state-rs sim))
   (T (simulator (simulator-step sim)))))

;; ---- Proofs ----

(definec simulator* (data :data steps :nat) :data
  :ic (>= (len data) steps)
  (simulator (list data '() steps)))

(definec take2 (data :tl n :nat) :tl
  :ic (>= (len data) n)
  (if (zp n)
      '()
    (cons (car data) (take2 (cdr data) (1- n)))))

;; Checks if x is a prefix of y
(definec prefixp (x :tl y :tl) :bool
  (cond
   ((lendp x) T)
   ((lendp y) (lendp x))
   (T (and (equal (car x) (car y))
	   (prefixp (cdr x) (cdr y))))))

(defthm take2-always-a-prefix
  (implies (and (tlp x)
		(natp n)
		(>= (len x) n))
	   (prefixp (take2 x n) x)))

(defthm take2-sim-relation
  (implies (and (sim-statep sim)
		(>= (len (sim-state-ss sim)) (sim-state-steps sim)))
	   (equal (simulator sim)
		  (app (sim-state-rs sim)
		       (take2 (sim-state-ss sim) (sim-state-steps sim))))))

(defthm sim*-equiv-take2
  (implies (and (datap d)
		(natp n)
		(>= (len d) n))
	   (equal (simulator* d n) (take2 d n))))

(defthm data-never-out-of-order
  (implies (and (datap d)
		(natp n)
		(>= (len d) n))
	   (prefixp (simulator* d n) d)))

