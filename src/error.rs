// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// All files in the project carrying such notice may not be copied, modified, or distributed
// except according to those terms.

//! Wrap several flavors of Windows error into a `Result`.

use std::fmt;

use failure::Fail;

use winapi::shared::minwindef::DWORD;
use winapi::shared::winerror::{FACILITY_WIN32, HRESULT, HRESULT_FROM_WIN32, SUCCEEDED};
use winapi::um::errhandlingapi::GetLastError;

/// A (Win32 error code)
/// [https://docs.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/18d8fbe8-a967-4f1c-ae50-99ca8e491d2d],
/// usually from `GetLastError()`.
///
/// Includes optional function name, source file name, and line number.
#[derive(Clone, Debug, Default, Eq, Fail, PartialEq)]
pub struct Win32Error {
    /// The error code.
    pub code: DWORD,
    /// The name of the function that failed.
    pub function: Option<&'static str>,
    /// The file and line of the failing function call.
    pub file_line: Option<FileLine>,
}

/// An (HRESULT error code)
/// [https://docs.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/0642cb2f-2075-4469-918c-4441e69c548a].
/// These usually come from COM APIs.
///
/// Includes optional function name, source file name, and line number.
#[derive(Clone, Debug, Default, Eq, Fail, PartialEq)]
pub struct HResult {
    /// The error code
    pub hr: HRESULT,
    /// The name of the function that failed.
    pub function: Option<&'static str>,
    /// The file and line of the failing function call.
    pub file_line: Option<FileLine>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FileLine(pub &'static str, pub u32);

impl Win32Error {
    /// Create from an error code.
    pub fn new(code: DWORD) -> Self {
        Win32Error {
            code,
            function: None,
            file_line: None,
        }
    }

    /// Create from `GetLastError()`
    pub fn get_last_error() -> Self {
        Win32Error::new(unsafe { GetLastError() })
    }

    /// Add the name of the failing function to the error.
    pub fn function(self, function: &'static str) -> Self {
        Self {
            function: Some(function),
            ..self
        }
    }

    /// Add the source file name and line number of the call to the error.
    pub fn file_line(self, file: &'static str, line: u32) -> Self {
        Self {
            file_line: Some(FileLine(file, line)),
            ..self
        }
    }
}

impl HResult {
    /// Create from an `HRESULT`.
    pub fn new(hr: HRESULT) -> Self {
        HResult {
            hr,
            function: None,
            file_line: None,
        }
    }
    /// Add the name of the failing function to the error.
    pub fn function(self, function: &'static str) -> Self {
        Self {
            function: Some(function),
            ..self
        }
    }

    /// Add the source file name and line number of the call to the error.
    pub fn file_line(self, file: &'static str, line: u32) -> Self {
        Self {
            file_line: Some(FileLine(file, line)),
            ..self
        }
    }

    /// Get the result code portion of the `HRESULT`
    pub fn extract_code(&self) -> HRESULT {
        // from winerror.h HRESULT_CODE macro
        self.hr & 0xFFFF
    }

    /// Get the facility portion of the `HRESULT`
    pub fn extract_facility(&self) -> HRESULT {
        // from winerror.h HRESULT_FACILITY macro
        (self.hr >> 16) & 0x1fff
    }

    /// If the `HResult` corresponds to a Win32 error, convert.
    ///
    /// Returns the original `HResult` as an error on failure.
    pub fn try_into_win32_err(self) -> Result<Win32Error, Self> {
        if self.extract_facility() == FACILITY_WIN32 {
            Ok(Win32Error {
                code: self.extract_code() as DWORD,
                function: self.function,
                file_line: self.file_line,
            })
        } else {
            Err(self)
        }
    }
}

impl fmt::Display for Win32Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if let Some(function) = self.function {
            if let Some(FileLine(file, line)) = self.file_line {
                write!(f, "{}:{} ", file, line)?;
            }

            write!(f, "{} ", function)?;

            write!(f, "failed, ")?;
        }

        write!(f, "{:#010x}", self.code)?;

        Ok(())
    }
}

impl fmt::Display for HResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if let Some(function) = self.function {
            if let Some(FileLine(file, line)) = self.file_line {
                write!(f, "{}:{} ", file, line)?;
            }

            write!(f, "{} ", function)?;

            if !SUCCEEDED(self.hr) {
                write!(f, "failed. ")?;
            } else {
                write!(f, "returned ")?;
            }
        }

        write!(f, "HRESULT {:#010x}", self.hr)?;

        Ok(())
    }
}

/// Trait for adding information to a `Result<T, Error>`.
pub trait ResultExt<T, E> {
    type Code;

    /// Add the name of the failing function to the error.
    fn function(self, function: &'static str) -> Result<T, E>;

    /// Add the source file name and line number of the call to the error.
    fn file_line(self, file: &'static str, line: u32) -> Result<T, E>;

    /// Replace `Err(code)` with `replacement`.
    fn allow_err(self, code: Self::Code, replacement: T) -> Result<T, E>;

    /// Replace `Err(code)` with the result of calling `replacement()`.
    fn allow_err_with<F>(self, code: Self::Code, replacement: F) -> Result<T, E>
    where
        F: FnOnce() -> T;
}

impl<T> ResultExt<T, HResult> for Result<T, HResult> {
    type Code = HRESULT;
    fn function(self, function: &'static str) -> Self {
        self.map_err(|e| e.function(function))
    }

    fn file_line(self, file: &'static str, line: u32) -> Self {
        self.map_err(|e| e.file_line(file, line))
    }

    fn allow_err(self, code: Self::Code, replacement: T) -> Self {
        match self {
            Ok(r) => Ok(r),
            Err(ref e) if e.hr == code => Ok(replacement),
            Err(e) => Err(e),
        }
    }

    fn allow_err_with<F>(self, code: Self::Code, replacement: F) -> Self
    where
        F: FnOnce() -> T,
    {
        match self {
            Ok(r) => Ok(r),
            Err(ref e) if e.hr == code => Ok(replacement()),
            Err(e) => Err(e),
        }
    }
}

impl<T> ResultExt<T, Win32Error> for Result<T, Win32Error> {
    type Code = DWORD;
    fn function(self, function: &'static str) -> Self {
        self.map_err(|e| e.function(function))
    }

    fn file_line(self, file: &'static str, line: u32) -> Self {
        self.map_err(|e| e.file_line(file, line))
    }

    fn allow_err(self, code: Self::Code, replacement: T) -> Self {
        match self {
            Ok(r) => Ok(r),
            Err(ref e) if e.code == code => Ok(replacement),
            Err(e) => Err(e),
        }
    }

    fn allow_err_with<F>(self, code: Self::Code, replacement: F) -> Self
    where
        F: FnOnce() -> T,
    {
        match self {
            Ok(r) => Ok(r),
            Err(ref e) if e.code == code => Ok(replacement()),
            Err(e) => Err(e),
        }
    }
}

impl From<Win32Error> for HResult {
    fn from(win32_error: Win32Error) -> Self {
        HResult {
            hr: HRESULT_FROM_WIN32(win32_error.code),
            function: win32_error.function,
            file_line: win32_error.file_line,
        }
    }
}

/// Convert an `HRESULT` into a `Result`.
pub fn succeeded_or_err(hr: HRESULT) -> Result<HRESULT, HResult> {
    if !SUCCEEDED(hr) {
        Err(HResult::new(hr))
    } else {
        Ok(hr)
    }
}

/// Call a function that returns an `HRESULT`, convert to a `Result`.
///
/// The error will be augmented with the name of the function and the file and line number of
/// the macro usage.
///
/// # Example
/// ```ignore
/// unsafe {
///     check_succeeded!(
///         CoInitialize(std::ptr::null_mut())
///     )?;
/// }
/// ```
#[macro_export]
macro_rules! check_succeeded {
    ($f:ident ( $($arg:expr),* )) => {
        {
            use $crate::error::ResultExt;
            $crate::error::succeeded_or_err($f($($arg),*))
                .function(stringify!($f))
                .file_line(file!(), line!())
        }
    };

    // support for trailing comma in argument list
    ($f:ident ( $($arg:expr),+ , )) => {
        $crate::check_succeeded!($f($($arg),+))
    };
}

/// Convert an integer return value into a `Result`, using `GetLastError()` if zero.
pub fn true_or_last_err<T>(rv: T) -> Result<T, Win32Error>
where
    T: Eq,
    T: From<bool>,
{
    if rv == T::from(false) {
        Err(Win32Error::get_last_error())
    } else {
        Ok(rv)
    }
}

/// Call a function that returns a integer, conver to a `Result`, using `GetLastError()` if zero.
///
/// The error will be augmented with the name of the function and the file and line number of
/// the macro usage.
///
/// # Example
/// ```ignore
/// unsafe {
///     check_true!(
///         FlushFileBuffers(file)
///     )?;
/// }
/// ```
#[macro_export]
macro_rules! check_true {
    ($f:ident ( $($arg:expr),* )) => {
        {
            use $crate::error::ResultExt;
            $crate::error::true_or_last_err($f($($arg),*))
                .function(stringify!($f))
                .file_line(file!(), line!())
        }
    };

    // support for trailing comma in argument list
    ($f:ident ( $($arg:expr),+ , )) => {
        $crate::check_true!($f($($arg),+))
    };
}
