// This file is based on cpp-peglib https://github.com/yhirose/cpp-peglib

//
//  peglib.h
//
//  Copyright (c) 2020 Yuji Hirose. All rights reserved.
//  MIT License
//

#pragma once


//#if !defined(__cplusplus) || __cplusplus < 201703L
//#error "Requires complete C++17 support"
//#endif

#define USE_EASTL 1

#if USE_EASTL

#define STL eastl

#include <EASTL/algorithm.h>
#include <EASTL/any.h>
#include <EASTL/tuple.h>
#include <EASTL/shared_ptr.h>
#include <cassert>
#include <cctype>
#include <cstring>
#include <EASTL/functional.h>
#include <EASTL/initializer_list.h>
#include <iostream>
#include <limits>
#include <EASTL/list.h>
#include <EASTL/map.h>
#include <EASTL/memory.h>
#include <EASTL/set.h>
#include <EASTL/string.h>
#include <EASTL/string_view.h>
#include <EASTL/unordered_map.h>
#include <EASTL/vector.h>
#include <EASTL/type_traits.h>

#else

#include <algorithm>
#include <any>
#include <cassert>
#include <cctype>
#include <cstring>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <limits>
#include <list>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#define STL std

#endif

namespace peg {


/*-----------------------------------------------------------------------------
 *  scope_exit
 *---------------------------------------------------------------------------*/

// This is based on
// "http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2014/n4189".

template <typename EF> struct scope_exit {
  explicit scope_exit(EF &&f)
      : exit_function(STL::move(f)), execute_on_destruction{true} {}

  scope_exit(scope_exit &&rhs)
      : exit_function(STL::move(rhs.exit_function)),
        execute_on_destruction{rhs.execute_on_destruction} {
    rhs.release();
  }

  ~scope_exit() {
    if (execute_on_destruction) { this->exit_function(); }
  }

  void release() { this->execute_on_destruction = false; }

private:
  scope_exit(const scope_exit &) = delete;
  void operator=(const scope_exit &) = delete;
  scope_exit &operator=(scope_exit &&) = delete;

  EF exit_function;
  bool execute_on_destruction;
};

template <typename T>
inline auto make_scope_exit(T&& func) {
  return scope_exit<T>(STL::forward<T>(func));
}

/*-----------------------------------------------------------------------------*/

struct OnceFlag {
  bool val = false;
};

template <typename T> void call_once(OnceFlag &flag, T& func)  {
  if (!flag.val) {
    func();
    flag.val = true;
  }
};

/*-----------------------------------------------------------------------------
 *  UTF8 functions
 *---------------------------------------------------------------------------*/

inline size_t codepoint_length(const char *s8, size_t l) {
  if (l) {
    uint8_t b = static_cast<uint8_t>(s8[0]);
    if ((b & 0x80) == 0) {
      return 1;
    } else if ((b & 0xE0) == 0xC0 && l >= 2) {
      return 2;
    } else if ((b & 0xF0) == 0xE0 && l >= 3) {
      return 3;
    } else if ((b & 0xF8) == 0xF0 && l >= 4) {
      return 4;
    }
  }
  return 0;
}

inline size_t encode_codepoint(char32_t cp, char *buff) {
  if (cp < 0x0080) {
    buff[0] = static_cast<char>(cp & 0x7F);
    return 1;
  } else if (cp < 0x0800) {
    buff[0] = static_cast<char>(0xC0 | ((cp >> 6) & 0x1F));
    buff[1] = static_cast<char>(0x80 | (cp & 0x3F));
    return 2;
  } else if (cp < 0xD800) {
    buff[0] = static_cast<char>(0xE0 | ((cp >> 12) & 0xF));
    buff[1] = static_cast<char>(0x80 | ((cp >> 6) & 0x3F));
    buff[2] = static_cast<char>(0x80 | (cp & 0x3F));
    return 3;
  } else if (cp < 0xE000) {
    // D800 - DFFF is invalid...
    return 0;
  } else if (cp < 0x10000) {
    buff[0] = static_cast<char>(0xE0 | ((cp >> 12) & 0xF));
    buff[1] = static_cast<char>(0x80 | ((cp >> 6) & 0x3F));
    buff[2] = static_cast<char>(0x80 | (cp & 0x3F));
    return 3;
  } else if (cp < 0x110000) {
    buff[0] = static_cast<char>(0xF0 | ((cp >> 18) & 0x7));
    buff[1] = static_cast<char>(0x80 | ((cp >> 12) & 0x3F));
    buff[2] = static_cast<char>(0x80 | ((cp >> 6) & 0x3F));
    buff[3] = static_cast<char>(0x80 | (cp & 0x3F));
    return 4;
  }
  return 0;
}

inline STL::string encode_codepoint(char32_t cp) {
  char buff[4];
  size_t l = encode_codepoint(cp, buff);
  return STL::string(buff, l);
}

inline bool decode_codepoint(const char *s8, size_t l, size_t &bytes,
                             char32_t &cp) {
  if (l) {
    uint8_t b = static_cast<uint8_t>(s8[0]);
    if ((b & 0x80) == 0) {
      bytes = 1;
      cp = b;
      return true;
    } else if ((b & 0xE0) == 0xC0) {
      if (l >= 2) {
        bytes = 2;
        cp = ((static_cast<char32_t>(s8[0] & 0x1F)) << 6) |
             (static_cast<char32_t>(s8[1] & 0x3F));
        return true;
      }
    } else if ((b & 0xF0) == 0xE0) {
      if (l >= 3) {
        bytes = 3;
        cp = ((static_cast<char32_t>(s8[0] & 0x0F)) << 12) |
             ((static_cast<char32_t>(s8[1] & 0x3F)) << 6) |
             (static_cast<char32_t>(s8[2] & 0x3F));
        return true;
      }
    } else if ((b & 0xF8) == 0xF0) {
      if (l >= 4) {
        bytes = 4;
        cp = ((static_cast<char32_t>(s8[0] & 0x07)) << 18) |
             ((static_cast<char32_t>(s8[1] & 0x3F)) << 12) |
             ((static_cast<char32_t>(s8[2] & 0x3F)) << 6) |
             (static_cast<char32_t>(s8[3] & 0x3F));
        return true;
      }
    }
  }
  return false;
}

inline size_t decode_codepoint(const char *s8, size_t l, char32_t &out) {
  size_t bytes;
  if (decode_codepoint(s8, l, bytes, out)) { return bytes; }
  return 0;
}

inline char32_t decode_codepoint(const char *s8, size_t l) {
  char32_t out = 0;
  decode_codepoint(s8, l, out);
  return out;
}

inline STL::u32string decode(const char *s8, size_t l) {
  STL::u32string out;
  size_t i = 0;
  while (i < l) {
    size_t beg = i++;
    while (i < l && (s8[i] & 0xc0) == 0x80) {
      i++;
    }
    out += decode_codepoint(&s8[beg], (i - beg));
  }
  return out;
}

/*-----------------------------------------------------------------------------
 *  escape_characters
 *---------------------------------------------------------------------------*/

inline STL::string escape_characters(const char *s, size_t n) {
  STL::string str;
  for (size_t i = 0; i < n; i++) {
    char c = s[i];
    switch (c) {
    case '\n': str += "\\n"; break;
    case '\r': str += "\\r"; break;
    case '\t': str += "\\t"; break;
    default: str += c; break;
    }
  }
  return str;
}

inline STL::string escape_characters(STL::string_view sv) {
  return escape_characters(sv.data(), sv.size());
}

/*-----------------------------------------------------------------------------
 *  resolve_escape_sequence
 *---------------------------------------------------------------------------*/

inline bool is_hex(char c, int &v) {
  if ('0' <= c && c <= '9') {
    v = c - '0';
    return true;
  } else if ('a' <= c && c <= 'f') {
    v = c - 'a' + 10;
    return true;
  } else if ('A' <= c && c <= 'F') {
    v = c - 'A' + 10;
    return true;
  }
  return false;
}

inline bool is_digit(char c, int &v) {
  if ('0' <= c && c <= '9') {
    v = c - '0';
    return true;
  }
  return false;
}

inline STL::pair<int, size_t> parse_hex_number(const char *s, size_t n,
                                               size_t i) {
  int ret = 0;
  int val;
  while (i < n && is_hex(s[i], val)) {
    ret = static_cast<int>(ret * 16 + val);
    i++;
  }
  return STL::pair<int, size_t>(ret, i);
}

inline STL::pair<int, size_t> parse_octal_number(const char *s, size_t n,
                                                 size_t i) {
  int ret = 0;
  int val;
  while (i < n && is_digit(s[i], val)) {
    ret = static_cast<int>(ret * 8 + val);
    i++;
  }
  return STL::pair<int, size_t>(ret, i);
}

inline STL::string resolve_escape_sequence(const char *s, size_t n) {
  STL::string r;
  r.reserve(n);

  size_t i = 0;
  while (i < n) {
    char ch = s[i];
    if (ch == '\\') {
      i++;
      if (i == n) { throw std::runtime_error("Invalid escape sequence..."); }
      switch (s[i]) {
      case 'n':
        r += '\n';
        i++;
        break;
      case 'r':
        r += '\r';
        i++;
        break;
      case 't':
        r += '\t';
        i++;
        break;
      case '\'':
        r += '\'';
        i++;
        break;
      case '"':
        r += '"';
        i++;
        break;
      case '[':
        r += '[';
        i++;
        break;
      case ']':
        r += ']';
        i++;
        break;
      case '\\':
        r += '\\';
        i++;
        break;
      case 'x':
      case 'u': {
        char32_t cp;
        STL::tie(cp, i) = parse_hex_number(s, n, i + 1);
        r += encode_codepoint(cp);
        break;
      }
      default: {
        char32_t cp;
        STL::tie(cp, i) = parse_octal_number(s, n, i);
        r += encode_codepoint(cp);
        break;
      }
      }
    } else {
      r += ch;
      i++;
    }
  }
  return r;
}

/*-----------------------------------------------------------------------------
 *  Trie
 *---------------------------------------------------------------------------*/

class Trie {
public:
  Trie() = default;
  Trie(const Trie &) = default;

  Trie(const STL::vector<STL::string> &items) {
    for (const STL::string &item : items) {
      for (size_t len = 1; len <= item.size(); len++) {
        bool last = len == item.size();
        STL::string_view sv(item.data(), len);
        auto it = dic_.find(sv);
        if (it == dic_.end()) {
          dic_.emplace(sv, Info{last, last});
        } else if (last) {
          it->second.match = true;
        } else {
          it->second.done = false;
        }
      }
    }
  }

  size_t match(const char *text, size_t text_len) const {
    size_t match_len = 0;
    bool done = false;
    size_t len = 1;
    while (!done && len <= text_len) {
      STL::string_view sv(text, len);
      auto it = dic_.find(sv);
      if (it == dic_.end()) {
        done = true;
      } else {
        if (it->second.match) { match_len = len; }
        if (it->second.done) { done = true; }
      }
      len += 1;
    }
    return match_len;
  }

private:
  struct Info {
    bool done;
    bool match;
  };

  // TODO: Use unordered_map when heterogeneous lookup is supported in C++20
  // STL::unordered_map<STL::string, Info> dic_;
  STL::map<STL::string_view, Info, STL::less<>> dic_;
};

/*-----------------------------------------------------------------------------
 *  PEG
 *---------------------------------------------------------------------------*/

/*
 * Line information utility function
 */
inline STL::pair<size_t, size_t> line_info(const char *start, const char *cur) {
  const char* p = start;
  const char* col_ptr = p;
  size_t no = 1;

  while (p < cur) {
    if (*p == '\n') {
      no++;
      col_ptr = p + 1;
    }
    p++;
  }

  size_t col = p - col_ptr + 1;

  return STL::make_pair(no, col);
}

/*
 * String tag
 */
inline constexpr unsigned int str2tag_core(const char *s, size_t l,
                                           unsigned int h) {
  return (l == 0) ? h
                  : str2tag_core(s + 1, l - 1,
                                 (h * 33) ^ static_cast<unsigned char>(*s));
}

inline constexpr unsigned int str2tag(STL::string_view sv) {
  return str2tag_core(sv.data(), sv.size(), 0);
}

namespace udl {

inline constexpr unsigned int operator"" _(const char *s, size_t l) {
  return str2tag_core(s, l, 0);
}

} // namespace udl

template <typename Function> struct RetTypeHelper;

template <class Ret>
struct RetTypeHelper<Ret(*)()> {
    using type = Ret;
};

template <class Ret, typename... Args>
struct RetTypeHelper<Ret(*)(Args...)> {
    using type = Ret;
};

/*
 * Semantic values
 */
struct SemanticValues : protected STL::vector<STL::any> {
  // Input text
  const char *path = nullptr;
  const char *ss = nullptr;
  const STL::vector<size_t> *source_line_index = nullptr;

  // Matched string
  STL::string_view sv() const { return sv_; }

  // Definition name
  const STL::string &name() const { return name_; }

  STL::vector<unsigned int> tags;

  // Line number and column at which the matched string is
  STL::pair<size_t, size_t> line_info() const {
    const STL::vector<size_t> &idx = *source_line_index;

    size_t cur = static_cast<size_t>(STL::distance(ss, sv_.data()));
    auto it = STL::lower_bound(
        idx.begin(), idx.end(), cur,
        [](size_t element, size_t value) { return element < value; });

    size_t id = static_cast<size_t>(STL::distance(idx.begin(), it));
    size_t off = cur - (id == 0 ? 0 : idx[id - 1] + 1);
    return STL::make_pair(id + 1, off + 1);
  }

  // Choice count
  size_t choice_count() const { return choice_count_; }

  // Choice number (0 based index)
  size_t choice() const { return choice_; }

  // Tokens
  STL::vector<STL::string_view> tokens;

  STL::string_view token(size_t id = 0) const {
    if (tokens.empty()) { return sv_; }
    assert(id < tokens.size());
    return tokens[id];
  }

  // Token conversion
  STL::string token_to_string(size_t id = 0) const {
    return STL::string(token(id));
  }

  //template <typename T> T token_to_number() const {
  //  auto sv = token();
  //  T n = 0;
  //  STL::from_chars(sv.data(), sv.data() + sv.size(), n);
  //  return n;
  //}

  // Transform the semantic value vector to another vector
  template <typename T>
  STL::vector<T> transform(size_t beg = 0,
                           size_t end = static_cast<size_t>(-1)) const {
    STL::vector<T> r;
    end = (STL::min)(end, size());
    for (size_t i = beg; i < end; i++) {
      r.emplace_back(STL::any_cast<T>((*this)[i]));
    }
    return r;
  }

  using STL::vector<STL::any>::iterator;
  using STL::vector<STL::any>::const_iterator;
  using STL::vector<STL::any>::size;
  using STL::vector<STL::any>::empty;
  using STL::vector<STL::any>::assign;
  using STL::vector<STL::any>::begin;
  using STL::vector<STL::any>::end;
  using STL::vector<STL::any>::rbegin;
  using STL::vector<STL::any>::rend;
  using STL::vector<STL::any>::operator[];
  using STL::vector<STL::any>::at;
  using STL::vector<STL::any>::resize;
  using STL::vector<STL::any>::front;
  using STL::vector<STL::any>::back;
  using STL::vector<STL::any>::push_back;
  using STL::vector<STL::any>::pop_back;
  using STL::vector<STL::any>::insert;
  using STL::vector<STL::any>::erase;
  using STL::vector<STL::any>::clear;
  using STL::vector<STL::any>::swap;
  using STL::vector<STL::any>::emplace;
  using STL::vector<STL::any>::emplace_back;

private:
  friend class Context;
  friend class Sequence;
  friend class PrioritizedChoice;
  friend class Holder;
  friend class PrecedenceClimbing;

  STL::string_view sv_;
  size_t choice_count_ = 0;
  size_t choice_ = 0;
  STL::string name_;
};



template <typename T>
struct argument_count : argument_count<decltype(&T::operator())> {};
template <typename R, typename... Args>
struct argument_count<R (*)(Args...)>
    : STL::integral_constant<unsigned, sizeof...(Args)> {};
template <typename R, typename C, typename... Args>
struct argument_count<R (C::*)(Args...)>
    : STL::integral_constant<unsigned, sizeof...(Args)> {};
template <typename R, typename C, typename... Args>
struct argument_count<R (C::*)(Args...) const>
    : STL::integral_constant<unsigned, sizeof...(Args)> {};

class Action {
public:
  using Fty = STL::function<STL::any(SemanticValues &vs, STL::any &dt)>;

  Action() = default;
  Action(Action &&rhs) = default;
  explicit Action(Fty fn) : fn_(fn) {}
  void operator=(Fty fn) { fn_ = fn; }
  Action &operator=(const Action &rhs) = default;

  operator bool() const { return bool(fn_); }

  STL::any operator()(SemanticValues &vs, STL::any &dt) const {
    return fn_(vs, dt);
  }

private:
  Fty fn_;
};

/*
 * Semantic predicate
 */
// Note: 'parse_error' exception class should be be used in sematic action
// handlers to reject the rule.
struct parse_error {
  parse_error() = default;
  parse_error(const char *s) : s_(s) {}
  const char *what() const { return s_.empty() ? nullptr : s_.data(); }

private:
  STL::string s_;
};

/*
 * Parse result helper
 */
inline bool success(size_t len) { return len != static_cast<size_t>(-1); }

inline bool fail(size_t len) { return len == static_cast<size_t>(-1); }

/*
 * Log
 */
using Log = STL::function<void(size_t, size_t, const STL::string &)>;

/*
 * ErrorInfo
 */
struct ErrorInfo {
  const char *error_pos = nullptr;
  STL::vector<STL::pair<const char *, bool>> expected_tokens;
  const char *message_pos = nullptr;
  STL::string message;

  void clear() {
    error_pos = nullptr;
    expected_tokens.clear();
    message_pos = nullptr;
    message.clear();
  }

  void add(const char *token, bool is_literal) {
    for (const auto &x : expected_tokens) {
      if (x.first == token && x.second == is_literal) { return; }
    }
    expected_tokens.push_back(STL::make_pair(token, is_literal));
  }

  void output_log(const Log &log, const char *s, size_t n) const {
    if (message_pos) {
      auto line = line_info(s, message_pos);
      STL::string msg;
      auto unexpected_token = heuristic_error_token(s, n, message_pos);
      if (!unexpected_token.empty()) {
        msg = replace_all(message, "%t", unexpected_token);
      } else {
        msg = message;
      }
      log(line.first, line.second, msg);
    } else if (error_pos) {
      auto line = line_info(s, error_pos);

      STL::string msg;
      if (expected_tokens.empty()) {
        msg = "syntax error.";
      } else {
        msg = "syntax error";

        // unexpected token
        auto unexpected_token = heuristic_error_token(s, n, error_pos);
        if (!unexpected_token.empty()) {
          msg += ", unexpected '";
          msg += unexpected_token;
          msg += "'";
        }

        bool first_item = true;
        size_t i = 0;
        while (i < expected_tokens.size()) {
          STL::pair<const char *, bool> pair = expected_tokens[expected_tokens.size() - i - 1];
          const char *token = pair.first;
          bool is_literal = pair.second;

          // Skip rules start with '_'
          if (!is_literal && token[0] != '_') {
            msg += (first_item ? ", expecting " : ", ");
            if (is_literal) {
              msg += "'";
              msg += token;
              msg += "'";
            } else {
              msg += "<";
              msg += token;
              msg += ">";
            }
            first_item = false;
          }

          i++;
        }
        msg += ".";
      }

      log(line.first, line.second, msg);
    }
  }

private:
  STL::string heuristic_error_token(const char *s, size_t n,
                                    const char *error_pos) const {
    ptrdiff_t len = n - STL::distance(s, error_pos);
    if (len) {
      int i = 0;
      int c = error_pos[i++];
      if (!std::ispunct(c) && !std::isspace(c)) {
        while (i < len && !std::ispunct(error_pos[i]) &&
               !std::isspace(error_pos[i])) {
          i++;
        }
      }
      return escape_characters(error_pos, STL::min<size_t>(i, 8));
    }
    return STL::string();
  }

  STL::string replace_all(STL::string str, const STL::string &from,
                          const STL::string &to) const {
    size_t pos = 0;
    while ((pos = str.find(from, pos)) != STL::string::npos) {
      str.replace(pos, from.length(), to);
      pos += to.length();
    }
    return str;
  }
};

/*
 * Context
 */
class Context;
class Ope;
class Definition;

using TracerEnter = STL::function<void(const Ope &name, const char *s, size_t n,
                                       const SemanticValues &vs,
                                       const Context &c, const STL::any &dt)>;

using TracerLeave = STL::function<void(
    const Ope &ope, const char *s, size_t n, const SemanticValues &vs,
    const Context &c, const STL::any &dt, size_t)>;

class Context {
public:
  const char *path;
  const char *s;
  const size_t l;
  STL::vector<size_t> source_line_index;

  ErrorInfo error_info;
  bool recovered = false;

  STL::vector<STL::shared_ptr<SemanticValues>> value_stack;
  size_t value_stack_size = 0;

  STL::vector<Definition *> rule_stack;
  STL::vector<STL::vector<STL::shared_ptr<Ope>>> args_stack;

  size_t in_token_boundary_count = 0;

  STL::shared_ptr<Ope> whitespaceOpe;
  bool in_whitespace = false;

  STL::shared_ptr<Ope> wordOpe;

  STL::vector<STL::map<STL::string_view, STL::string>> capture_scope_stack;
  size_t capture_scope_stack_size = 0;

  const size_t def_count;
  const bool enablePackratParsing;
  STL::vector<bool> cache_registered;
  STL::vector<bool> cache_success;

  STL::map<STL::pair<size_t, size_t>, STL::tuple<size_t, STL::any>>
      cache_values;

  TracerEnter tracer_enter;
  TracerLeave tracer_leave;

  Log log;

  Context(const char *path, const char *s, size_t l, size_t def_count,
          STL::shared_ptr<Ope> whitespaceOpe, STL::shared_ptr<Ope> wordOpe,
          bool enablePackratParsing, TracerEnter tracer_enter,
          TracerLeave tracer_leave, Log log)
      : path(path), s(s), l(l), whitespaceOpe(whitespaceOpe), wordOpe(wordOpe),
        def_count(def_count), enablePackratParsing(enablePackratParsing),
        cache_registered(enablePackratParsing ? def_count * (l + 1) : 0),
        cache_success(enablePackratParsing ? def_count * (l + 1) : 0),
        tracer_enter(tracer_enter), tracer_leave(tracer_leave), log(log) {

    for (size_t pos = 0; pos < l; pos++) {
      if (s[pos] == '\n') { source_line_index.push_back(pos); }
    }
    source_line_index.push_back(l);

    args_stack.resize(1);

    push_capture_scope();
  }

  ~Context() { assert(!value_stack_size); }

  Context(const Context &) = delete;
  Context(Context &&) = delete;
  Context operator=(const Context &) = delete;

  template <typename T>
  void packrat(const char *a_s, size_t def_id, size_t &len, STL::any &val,
               T fn) {
    if (!enablePackratParsing) {
      fn(val);
      return;
    }

    ptrdiff_t col = a_s - s;
    size_t idx = def_count * static_cast<size_t>(col) + def_id;

    if (cache_registered[idx]) {
      if (cache_success[idx]) {
        auto key = STL::make_pair(col, def_id);
        STL::tie(len, val) = cache_values[key];
        return;
      } else {
        len = static_cast<size_t>(-1);
        return;
      }
    } else {
      fn(val);
      cache_registered[idx] = true;
      cache_success[idx] = success(len);
      if (success(len)) {
        auto key = STL::make_pair(col, def_id);
        cache_values[key] = STL::make_pair(len, val);
      }
      return;
    }
  }

  SemanticValues &push() {
    assert(value_stack_size <= value_stack.size());
    if (value_stack_size == value_stack.size()) {
      value_stack.emplace_back(STL::make_shared<SemanticValues>());
    } else {
      auto &vs = *value_stack[value_stack_size];
      if (!vs.empty()) {
        vs.clear();
        if (!vs.tags.empty()) { vs.tags.clear(); }
      }
      vs.sv_ = STL::string_view();
      vs.choice_count_ = 0;
      vs.choice_ = 0;
      if (!vs.tokens.empty()) { vs.tokens.clear(); }
    }

    auto &vs = *value_stack[value_stack_size++];
    vs.path = path;
    vs.ss = s;
    vs.source_line_index = &source_line_index;
    return vs;
  }

  void pop() { value_stack_size--; }

  void push_args(STL::vector<STL::shared_ptr<Ope>> &&args) {
    args_stack.emplace_back(args);
  }

  void pop_args() { args_stack.pop_back(); }

  const STL::vector<STL::shared_ptr<Ope>> &top_args() const {
    return args_stack[args_stack.size() - 1];
  }

  void push_capture_scope() {
    assert(capture_scope_stack_size <= capture_scope_stack.size());
    if (capture_scope_stack_size == capture_scope_stack.size()) {
      capture_scope_stack.emplace_back(
          STL::map<STL::string_view, STL::string>());
    } else {
      auto &cs = capture_scope_stack[capture_scope_stack_size];
      if (!cs.empty()) { cs.clear(); }
    }
    capture_scope_stack_size++;
  }

  void pop_capture_scope() { capture_scope_stack_size--; }

  void shift_capture_values() {
    assert(capture_scope_stack.size() >= 2);
    auto curr = &capture_scope_stack[capture_scope_stack_size - 1];
    auto prev = curr - 1;
    for (const auto &kv : *curr) {
      (*prev)[kv.first] = kv.second;
    }
  }

  void set_error_pos(const char *a_s, const char *literal = nullptr);

  // void trace_enter(const char *name, const char *a_s, size_t n,
  void trace_enter(const Ope &ope, const char *a_s, size_t n,
                   SemanticValues &vs, STL::any &dt) const;
  // void trace_leave(const char *name, const char *a_s, size_t n,
  void trace_leave(const Ope &ope, const char *a_s, size_t n,
                   SemanticValues &vs, STL::any &dt, size_t len) const;
  bool is_traceable(const Ope &ope) const;

  mutable size_t next_trace_id = 0;
  mutable STL::list<size_t> trace_ids;
};

/*
 * Parser operators
 */
class Ope {
public:
  struct Visitor;

  virtual ~Ope() {}
  size_t parse(const char *s, size_t n, SemanticValues &vs, Context &c,
               STL::any &dt) const;
  virtual size_t parse_core(const char *s, size_t n, SemanticValues &vs,
                            Context &c, STL::any &dt) const = 0;
  virtual void accept(Visitor &v) = 0;
};

class Sequence : public Ope {
public:
  template <typename... Args>
  Sequence(const Args &... args)
      : opes_{static_cast<STL::shared_ptr<Ope>>(args)...} {}
  Sequence(const STL::vector<STL::shared_ptr<Ope>> &opes) : opes_(opes) {}
  Sequence(STL::vector<STL::shared_ptr<Ope>> &&opes) : opes_(opes) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    auto &chldsv = c.push();
    auto pop_se = make_scope_exit([&]() { c.pop(); });
    size_t i = 0;
    for (const auto &ope : opes_) {
      const auto &rule = *ope;
      size_t len = rule.parse(s + i, n - i, chldsv, c, dt);
      if (fail(len)) { return len; }
      i += len;
    }
    if (!chldsv.empty()) {
      for (size_t j = 0; j < chldsv.size(); j++) {
        vs.emplace_back(STL::move(chldsv[j]));
      }
    }
    if (!chldsv.tags.empty()) {
      for (size_t j = 0; j < chldsv.tags.size(); j++) {
        vs.tags.emplace_back(STL::move(chldsv.tags[j]));
      }
    }
    vs.sv_ = chldsv.sv_;
    if (!chldsv.tokens.empty()) {
      for (size_t j = 0; j < chldsv.tokens.size(); j++) {
        vs.tokens.emplace_back(STL::move(chldsv.tokens[j]));
      }
    }
    return i;
  }

  void accept(Visitor &v) override;

  STL::vector<STL::shared_ptr<Ope>> opes_;
};

class PrioritizedChoice : public Ope {
public:
  template <typename... Args>
  PrioritizedChoice(const Args &... args)
      : opes_{static_cast<STL::shared_ptr<Ope>>(args)...} {}
  PrioritizedChoice(const STL::vector<STL::shared_ptr<Ope>> &opes)
      : opes_(opes) {}
  PrioritizedChoice(STL::vector<STL::shared_ptr<Ope>> &&opes) : opes_(opes) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    size_t id = 0;
    for (const auto &ope : opes_) {
      auto &chldsv = c.push();
      c.push_capture_scope();
      auto se = make_scope_exit([&]() {
        c.pop();
        c.pop_capture_scope();
      });

      size_t len = ope->parse(s, n, chldsv, c, dt);
      if (success(len)) {
        if (!chldsv.empty()) {
          for (size_t i = 0; i < chldsv.size(); i++) {
            vs.emplace_back(STL::move(chldsv[i]));
          }
        }
        if (!chldsv.tags.empty()) {
          for (size_t i = 0; i < chldsv.tags.size(); i++) {
            vs.tags.emplace_back(STL::move(chldsv.tags[i]));
          }
        }
        vs.sv_ = chldsv.sv_;
        vs.choice_count_ = opes_.size();
        vs.choice_ = id;
        if (!chldsv.tokens.empty()) {
          for (size_t i = 0; i < chldsv.tokens.size(); i++) {
            vs.tokens.emplace_back(STL::move(chldsv.tokens[i]));
          }
        }

        c.shift_capture_values();
        return len;
      }

      id++;
    }
    return static_cast<size_t>(-1);
  }

  void accept(Visitor &v) override;

  size_t size() const { return opes_.size(); }

  STL::vector<STL::shared_ptr<Ope>> opes_;
};

class Repetition : public Ope {
public:
  Repetition(const STL::shared_ptr<Ope> &ope, size_t min, size_t max)
      : ope_(ope), min_(min), max_(max) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    size_t count = 0;
    size_t i = 0;
    while (count < min_) {
      c.push_capture_scope();
      auto se = make_scope_exit([&]() { c.pop_capture_scope(); });
      const auto &rule = *ope_;
      size_t len = rule.parse(s + i, n - i, vs, c, dt);
      if (success(len)) {
        c.shift_capture_values();
      } else {
        return len;
      }
      i += len;
      count++;
    }

    while (n - i > 0 && count < max_) {
      c.push_capture_scope();
      auto se = make_scope_exit([&]() { c.pop_capture_scope(); });
      size_t save_sv_size = vs.size();
      size_t save_tok_size = vs.tokens.size();
      const auto &rule = *ope_;
      size_t len = rule.parse(s + i, n - i, vs, c, dt);
      if (success(len)) {
        c.shift_capture_values();
      } else {
        if (vs.size() != save_sv_size) {
          vs.erase(vs.begin() + static_cast<std::ptrdiff_t>(save_sv_size));
          vs.tags.erase(vs.tags.begin() +
                        static_cast<std::ptrdiff_t>(save_sv_size));
        }
        if (vs.tokens.size() != save_tok_size) {
          vs.tokens.erase(vs.tokens.begin() +
                          static_cast<std::ptrdiff_t>(save_tok_size));
        }
        break;
      }
      i += len;
      count++;
    }
    return i;
  }

  void accept(Visitor &v) override;

  bool is_zom() const {
    return min_ == 0 && max_ == STL::numeric_limits<size_t>::max();
  }

  static STL::shared_ptr<Repetition> zom(const STL::shared_ptr<Ope> &ope) {
    return STL::make_shared<Repetition>(ope, 0,
                                        STL::numeric_limits<size_t>::max());
  }

  static STL::shared_ptr<Repetition> oom(const STL::shared_ptr<Ope> &ope) {
    return STL::make_shared<Repetition>(ope, 1,
                                        STL::numeric_limits<size_t>::max());
  }

  static STL::shared_ptr<Repetition> opt(const STL::shared_ptr<Ope> &ope) {
    return STL::make_shared<Repetition>(ope, 0, 1);
  }

  STL::shared_ptr<Ope> ope_;
  size_t min_;
  size_t max_;
};

class AndPredicate : public Ope {
public:
  AndPredicate(const STL::shared_ptr<Ope> &ope) : ope_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues & /*vs*/,
                    Context &c, STL::any &dt) const override {
    auto &chldsv = c.push();
    c.push_capture_scope();
    auto se = make_scope_exit([&]() {
      c.pop();
      c.pop_capture_scope();
    });
    const auto &rule = *ope_;
    size_t len = rule.parse(s, n, chldsv, c, dt);
    if (success(len)) {
      return 0;
    } else {
      return len;
    }
  }

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
};

class NotPredicate : public Ope {
public:
  NotPredicate(const STL::shared_ptr<Ope> &ope) : ope_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues & /*vs*/,
                    Context &c, STL::any &dt) const override {
    auto &chldsv = c.push();
    c.push_capture_scope();
    auto se = make_scope_exit([&]() {
      c.pop();
      c.pop_capture_scope();
    });
    size_t len = ope_->parse(s, n, chldsv, c, dt);
    if (success(len)) {
      c.set_error_pos(s);
      return static_cast<size_t>(-1);
    } else {
      return 0;
    }
  }

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
};

class Dictionary : public Ope, public STL::enable_shared_from_this<Dictionary> {
public:
  Dictionary(const STL::vector<STL::string> &v) : trie_(v) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override;

  void accept(Visitor &v) override;

  Trie trie_;
};

class LiteralString : public Ope,
                      public STL::enable_shared_from_this<LiteralString> {
public:
  LiteralString(STL::string &&s, bool ignore_case)
      : lit_(s), ignore_case_(ignore_case), is_word_(false) {}

  LiteralString(const STL::string &s, bool ignore_case)
      : lit_(s), ignore_case_(ignore_case), is_word_(false) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override;

  void accept(Visitor &v) override;

  STL::string lit_;
  bool ignore_case_;
  mutable OnceFlag init_is_word_;
  mutable bool is_word_;
};

class CharacterClass : public Ope,
                       public STL::enable_shared_from_this<CharacterClass> {
public:
  CharacterClass(const STL::string &s, bool negated) : negated_(negated) {
    STL::u32string chars = decode(s.data(), s.length());
    size_t i = 0;
    while (i < chars.size()) {
      if (i + 2 < chars.size() && chars[i + 1] == '-') {
        char32_t cp1 = chars[i];
        char32_t cp2 = chars[i + 2];
        ranges_.emplace_back(STL::make_pair(cp1, cp2));
        i += 3;
      } else {
        char32_t cp = chars[i];
        ranges_.emplace_back(STL::make_pair(cp, cp));
        i += 1;
      }
    }
    assert(!ranges_.empty());
  }

  CharacterClass(const STL::vector<STL::pair<char32_t, char32_t>> &ranges,
                 bool negated)
      : ranges_(ranges), negated_(negated) {
    assert(!ranges_.empty());
  }

  size_t parse_core(const char *s, size_t n, SemanticValues & /*vs*/,
                    Context &c, STL::any & /*dt*/) const override {
    if (n < 1) {
      c.set_error_pos(s);
      return static_cast<size_t>(-1);
    }

    char32_t cp = 0;
    size_t len = decode_codepoint(s, n, cp);

    for (const auto &range : ranges_) {
      if (range.first <= cp && cp <= range.second) {
        if (negated_) {
          c.set_error_pos(s);
          return static_cast<size_t>(-1);
        } else {
          return len;
        }
      }
    }

    if (negated_) {
      return len;
    } else {
      c.set_error_pos(s);
      return static_cast<size_t>(-1);
    }
  }

  void accept(Visitor &v) override;

  STL::vector<STL::pair<char32_t, char32_t>> ranges_;
  bool negated_;
};

class Character : public Ope, public STL::enable_shared_from_this<Character> {
public:
  Character(char ch) : ch_(ch) {}

  size_t parse_core(const char *s, size_t n, SemanticValues & /*vs*/,
                    Context &c, STL::any & /*dt*/) const override {
    if (n < 1 || s[0] != ch_) {
      c.set_error_pos(s);
      return static_cast<size_t>(-1);
    }
    return 1;
  }

  void accept(Visitor &v) override;

  char ch_;
};

class AnyCharacter : public Ope,
                     public STL::enable_shared_from_this<AnyCharacter> {
public:
  size_t parse_core(const char *s, size_t n, SemanticValues & /*vs*/,
                    Context &c, STL::any & /*dt*/) const override {
    size_t len = codepoint_length(s, n);
    if (len < 1) {
      c.set_error_pos(s);
      return static_cast<size_t>(-1);
    }
    return len;
  }

  void accept(Visitor &v) override;
};

class CaptureScope : public Ope {
public:
  CaptureScope(const STL::shared_ptr<Ope> &ope) : ope_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    c.push_capture_scope();
    auto se = make_scope_exit([&]() { c.pop_capture_scope(); });
    const auto &rule = *ope_;
    size_t len = rule.parse(s, n, vs, c, dt);
    return len;
  }

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
};

class Capture : public Ope {
public:
  using MatchAction = STL::function<void(const char *s, size_t n, Context &c)>;

  Capture(const STL::shared_ptr<Ope> &ope, MatchAction ma)
      : ope_(ope), match_action_(ma) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    const auto &rule = *ope_;
    size_t len = rule.parse(s, n, vs, c, dt);
    if (success(len) && match_action_) { match_action_(s, len, c); }
    return len;
  }

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
  MatchAction match_action_;
};

class TokenBoundary : public Ope {
public:
  TokenBoundary(const STL::shared_ptr<Ope> &ope) : ope_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override;

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
};

class Ignore : public Ope {
public:
  Ignore(const STL::shared_ptr<Ope> &ope) : ope_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues & /*vs*/,
                    Context &c, STL::any &dt) const override {
    const auto &rule = *ope_;
    auto &chldsv = c.push();
    auto se = make_scope_exit([&]() { c.pop(); });
    return rule.parse(s, n, chldsv, c, dt);
  }

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
};

using Parser = STL::function<size_t(const char *s, size_t n, SemanticValues &vs,
                                    STL::any &dt)>;

class User : public Ope {
public:
  User(Parser fn) : fn_(fn) {}
  size_t parse_core(const char *s, size_t n, SemanticValues &vs,
                    Context & /*c*/, STL::any &dt) const override {
    assert(fn_);
    return fn_(s, n, vs, dt);
  }
  void accept(Visitor &v) override;
  STL::function<size_t(const char *s, size_t n, SemanticValues &vs,
                       STL::any &dt)>
      fn_;
};

class WeakHolder : public Ope {
public:
  WeakHolder(const STL::shared_ptr<Ope> &ope) : weak_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    auto ope = weak_.lock();
    assert(ope);
    const auto &rule = *ope;
    return rule.parse(s, n, vs, c, dt);
  }

  void accept(Visitor &v) override;

  STL::weak_ptr<Ope> weak_;
};

class Holder : public Ope {
public:
  Holder(Definition *outer) : outer_(outer) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override;

  void accept(Visitor &v) override;

  STL::any reduce(SemanticValues &vs, STL::any &dt) const;

  const char *trace_name() const;

  STL::shared_ptr<Ope> ope_;
  Definition *outer_;
  mutable STL::string trace_name_;

  friend class Definition;
};

using Grammar = STL::unordered_map<STL::string, Definition>;

class Reference : public Ope, public STL::enable_shared_from_this<Reference> {
public:
  Reference(const Grammar &grammar, const STL::string &name, const char *s,
            bool is_macro, const STL::vector<STL::shared_ptr<Ope>> &args)
      : grammar_(grammar), name_(name), s_(s), is_macro_(is_macro), args_(args),
        rule_(nullptr), iarg_(0) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override;

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> get_core_operator() const;

  const Grammar &grammar_;
  const STL::string name_;
  const char *s_;

  const bool is_macro_;
  const STL::vector<STL::shared_ptr<Ope>> args_;

  Definition *rule_;
  size_t iarg_;
};

class Whitespace : public Ope {
public:
  Whitespace(const STL::shared_ptr<Ope> &ope) : ope_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    if (c.in_whitespace) { return 0; }
    c.in_whitespace = true;
    auto se = make_scope_exit([&]() { c.in_whitespace = false; });
    const auto &rule = *ope_;
    return rule.parse(s, n, vs, c, dt);
  }

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
};

class BackReference : public Ope {
public:
  BackReference(STL::string &&name) : name_(name) {}

  BackReference(const STL::string &name) : name_(name) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override;

  void accept(Visitor &v) override;

  STL::string name_;
};

class PrecedenceClimbing : public Ope {
public:
  using BinOpeInfo = STL::map<STL::string_view, STL::pair<size_t, char>>;

  PrecedenceClimbing(const STL::shared_ptr<Ope> &atom,
                     const STL::shared_ptr<Ope> &binop, const BinOpeInfo &info,
                     const Definition &rule)
      : atom_(atom), binop_(binop), info_(info), rule_(rule) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override {
    return parse_expression(s, n, vs, c, dt, 0);
  }

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> atom_;
  STL::shared_ptr<Ope> binop_;
  BinOpeInfo info_;
  const Definition &rule_;

private:
  size_t parse_expression(const char *s, size_t n, SemanticValues &vs,
                          Context &c, STL::any &dt, size_t min_prec) const;

  Definition &get_reference_for_binop(Context &c) const;
};

class Recovery : public Ope {
public:
  Recovery(const STL::shared_ptr<Ope> &ope) : ope_(ope) {}

  size_t parse_core(const char *s, size_t n, SemanticValues &vs, Context &c,
                    STL::any &dt) const override;

  void accept(Visitor &v) override;

  STL::shared_ptr<Ope> ope_;
};

/*
 * Factories
 */
template <typename... Args> STL::shared_ptr<Ope> seq(Args &&... args) {
  return STL::make_shared<Sequence>(static_cast<STL::shared_ptr<Ope>>(args)...);
}

template <typename... Args> STL::shared_ptr<Ope> cho(Args &&... args) {
  return STL::make_shared<PrioritizedChoice>(
      static_cast<STL::shared_ptr<Ope>>(args)...);
}

inline STL::shared_ptr<Ope> zom(const STL::shared_ptr<Ope> &ope) {
  return Repetition::zom(ope);
}

inline STL::shared_ptr<Ope> oom(const STL::shared_ptr<Ope> &ope) {
  return Repetition::oom(ope);
}

inline STL::shared_ptr<Ope> opt(const STL::shared_ptr<Ope> &ope) {
  return Repetition::opt(ope);
}

inline STL::shared_ptr<Ope> rep(const STL::shared_ptr<Ope> &ope, size_t min,
                                size_t max) {
  return STL::make_shared<Repetition>(ope, min, max);
}

inline STL::shared_ptr<Ope> apd(const STL::shared_ptr<Ope> &ope) {
  return STL::make_shared<AndPredicate>(ope);
}

inline STL::shared_ptr<Ope> npd(const STL::shared_ptr<Ope> &ope) {
  return STL::make_shared<NotPredicate>(ope);
}

inline STL::shared_ptr<Ope> dic(const STL::vector<STL::string> &v) {
  return STL::make_shared<Dictionary>(v);
}

inline STL::shared_ptr<Ope> lit(STL::string &&s) {
  return STL::make_shared<LiteralString>(s, false);
}

inline STL::shared_ptr<Ope> liti(STL::string &&s) {
  return STL::make_shared<LiteralString>(s, true);
}

inline STL::shared_ptr<Ope> cls(const STL::string &s) {
  return STL::make_shared<CharacterClass>(s, false);
}

inline STL::shared_ptr<Ope>
cls(const STL::vector<STL::pair<char32_t, char32_t>> &ranges) {
  return STL::make_shared<CharacterClass>(ranges, false);
}

inline STL::shared_ptr<Ope> ncls(const STL::string &s) {
  return STL::make_shared<CharacterClass>(s, true);
}

inline STL::shared_ptr<Ope>
ncls(const STL::vector<STL::pair<char32_t, char32_t>> &ranges) {
  return STL::make_shared<CharacterClass>(ranges, true);
}

inline STL::shared_ptr<Ope> chr(char dt) {
  return STL::make_shared<Character>(dt);
}

inline STL::shared_ptr<Ope> dot() { return STL::make_shared<AnyCharacter>(); }

inline STL::shared_ptr<Ope> csc(const STL::shared_ptr<Ope> &ope) {
  return STL::make_shared<CaptureScope>(ope);
}

inline STL::shared_ptr<Ope> cap(const STL::shared_ptr<Ope> &ope,
                                Capture::MatchAction ma) {
  return STL::make_shared<Capture>(ope, ma);
}

inline STL::shared_ptr<Ope> tok(const STL::shared_ptr<Ope> &ope) {
  return STL::make_shared<TokenBoundary>(ope);
}

inline STL::shared_ptr<Ope> ign(const STL::shared_ptr<Ope> &ope) {
  return STL::make_shared<Ignore>(ope);
}

inline STL::shared_ptr<Ope>
usr(STL::function<size_t(const char *s, size_t n, SemanticValues &vs,
                         STL::any &dt)>
        fn) {
  return STL::make_shared<User>(fn);
}

inline STL::shared_ptr<Ope> ref(const Grammar &grammar, const STL::string &name,
                                const char *s, bool is_macro,
                                const STL::vector<STL::shared_ptr<Ope>> &args) {
  return STL::make_shared<Reference>(grammar, name, s, is_macro, args);
}

inline STL::shared_ptr<Ope> wsp(const STL::shared_ptr<Ope> &ope) {
  return STL::make_shared<Whitespace>(STL::make_shared<Ignore>(ope));
}

inline STL::shared_ptr<Ope> bkr(STL::string &&name) {
  return STL::make_shared<BackReference>(name);
}

inline STL::shared_ptr<Ope> pre(const STL::shared_ptr<Ope> &atom,
                                const STL::shared_ptr<Ope> &binop,
                                const PrecedenceClimbing::BinOpeInfo &info,
                                const Definition &rule) {
  return STL::make_shared<PrecedenceClimbing>(atom, binop, info, rule);
}

inline STL::shared_ptr<Ope> rec(const STL::shared_ptr<Ope> &ope) {
  return STL::make_shared<Recovery>(ope);
}

/*
 * Visitor
 */
struct Ope::Visitor {
  virtual ~Visitor() {}
  virtual void visit(Sequence &) {}
  virtual void visit(PrioritizedChoice &) {}
  virtual void visit(Repetition &) {}
  virtual void visit(AndPredicate &) {}
  virtual void visit(NotPredicate &) {}
  virtual void visit(Dictionary &) {}
  virtual void visit(LiteralString &) {}
  virtual void visit(CharacterClass &) {}
  virtual void visit(Character &) {}
  virtual void visit(AnyCharacter &) {}
  virtual void visit(CaptureScope &) {}
  virtual void visit(Capture &) {}
  virtual void visit(TokenBoundary &) {}
  virtual void visit(Ignore &) {}
  virtual void visit(User &) {}
  virtual void visit(WeakHolder &) {}
  virtual void visit(Holder &) {}
  virtual void visit(Reference &) {}
  virtual void visit(Whitespace &) {}
  virtual void visit(BackReference &) {}
  virtual void visit(PrecedenceClimbing &) {}
  virtual void visit(Recovery &) {}
};

struct IsReference : public Ope::Visitor {
  void visit(Reference &) override { is_reference_ = true; }

  static bool check(Ope &ope) {
    IsReference vis;
    ope.accept(vis);
    return vis.is_reference_;
  }

private:
  bool is_reference_ = false;
};

struct TraceOpeName : public Ope::Visitor {
  void visit(Sequence &) override { name_ = "Sequence"; }
  void visit(PrioritizedChoice &) override { name_ = "PrioritizedChoice"; }
  void visit(Repetition &) override { name_ = "Repetition"; }
  void visit(AndPredicate &) override { name_ = "AndPredicate"; }
  void visit(NotPredicate &) override { name_ = "NotPredicate"; }
  void visit(Dictionary &) override { name_ = "Dictionary"; }
  void visit(LiteralString &) override { name_ = "LiteralString"; }
  void visit(CharacterClass &) override { name_ = "CharacterClass"; }
  void visit(Character &) override { name_ = "Character"; }
  void visit(AnyCharacter &) override { name_ = "AnyCharacter"; }
  void visit(CaptureScope &) override { name_ = "CaptureScope"; }
  void visit(Capture &) override { name_ = "Capture"; }
  void visit(TokenBoundary &) override { name_ = "TokenBoundary"; }
  void visit(Ignore &) override { name_ = "Ignore"; }
  void visit(User &) override { name_ = "User"; }
  void visit(WeakHolder &) override { name_ = "WeakHolder"; }
  void visit(Holder &ope) override { name_ = ope.trace_name(); }
  void visit(Reference &) override { name_ = "Reference"; }
  void visit(Whitespace &) override { name_ = "Whitespace"; }
  void visit(BackReference &) override { name_ = "BackReference"; }
  void visit(PrecedenceClimbing &) override { name_ = "PrecedenceClimbing"; }
  void visit(Recovery &) override { name_ = "Recovery"; }

  static STL::string get(Ope &ope) {
    TraceOpeName vis;
    ope.accept(vis);
    return vis.name_;
  }

private:
  const char *name_ = nullptr;
};

struct AssignIDToDefinition : public Ope::Visitor {
  void visit(Sequence &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(Repetition &ope) override { ope.ope_->accept(*this); }
  void visit(AndPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(NotPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(CaptureScope &ope) override { ope.ope_->accept(*this); }
  void visit(Capture &ope) override { ope.ope_->accept(*this); }
  void visit(TokenBoundary &ope) override { ope.ope_->accept(*this); }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(WeakHolder &ope) override { ope.weak_.lock()->accept(*this); }
  void visit(Holder &ope) override;
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override { ope.ope_->accept(*this); }
  void visit(PrecedenceClimbing &ope) override;
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

  STL::unordered_map<void *, size_t> ids;
};

struct IsLiteralToken : public Ope::Visitor {
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      if (!IsLiteralToken::check(*op)) { return; }
    }
    result_ = true;
  }

  void visit(Dictionary &) override { result_ = true; }
  void visit(LiteralString &) override { result_ = true; }

  static bool check(Ope &ope) {
    IsLiteralToken vis;
    ope.accept(vis);
    return vis.result_;
  }

private:
  bool result_ = false;
};

struct TokenChecker : public Ope::Visitor {
  void visit(Sequence &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(Repetition &ope) override { ope.ope_->accept(*this); }
  void visit(CaptureScope &ope) override { ope.ope_->accept(*this); }
  void visit(Capture &ope) override { ope.ope_->accept(*this); }
  void visit(TokenBoundary &) override { has_token_boundary_ = true; }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(WeakHolder &) override { has_rule_ = true; }
  void visit(Holder &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override { ope.ope_->accept(*this); }
  void visit(PrecedenceClimbing &ope) override { ope.atom_->accept(*this); }
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

  static bool is_token(Ope &ope) {
    if (IsLiteralToken::check(ope)) { return true; }

    TokenChecker vis;
    ope.accept(vis);
    return vis.has_token_boundary_ || !vis.has_rule_;
  }

private:
  bool has_token_boundary_ = false;
  bool has_rule_ = false;
};

struct FindLiteralToken : public Ope::Visitor {
  void visit(LiteralString &ope) override { token_ = ope.lit_.c_str(); }
  void visit(TokenBoundary &ope) override { ope.ope_->accept(*this); }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

  static const char *token(Ope &ope) {
    FindLiteralToken vis;
    ope.accept(vis);
    return vis.token_;
  }

private:
  const char *token_ = nullptr;
};

struct DetectLeftRecursion : public Ope::Visitor {
  DetectLeftRecursion(const STL::string &name) : name_(name) {}

  void visit(Sequence &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
      if (done_) {
        break;
      } else if (error_s) {
        done_ = true;
        break;
      }
    }
  }
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
      if (error_s) {
        done_ = true;
        break;
      }
    }
  }
  void visit(Repetition &ope) override {
    ope.ope_->accept(*this);
    done_ = ope.min_ > 0;
  }
  void visit(AndPredicate &ope) override {
    ope.ope_->accept(*this);
    done_ = false;
  }
  void visit(NotPredicate &ope) override {
    ope.ope_->accept(*this);
    done_ = false;
  }
  void visit(Dictionary &) override { done_ = true; }
  void visit(LiteralString &ope) override { done_ = !ope.lit_.empty(); }
  void visit(CharacterClass &) override { done_ = true; }
  void visit(Character &) override { done_ = true; }
  void visit(AnyCharacter &) override { done_ = true; }
  void visit(CaptureScope &ope) override { ope.ope_->accept(*this); }
  void visit(Capture &ope) override { ope.ope_->accept(*this); }
  void visit(TokenBoundary &ope) override { ope.ope_->accept(*this); }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(User &) override { done_ = true; }
  void visit(WeakHolder &ope) override { ope.weak_.lock()->accept(*this); }
  void visit(Holder &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override { ope.ope_->accept(*this); }
  void visit(BackReference &) override { done_ = true; }
  void visit(PrecedenceClimbing &ope) override { ope.atom_->accept(*this); }
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

  const char *error_s = nullptr;

private:
  STL::string name_;
  STL::set<STL::string> refs_;
  bool done_ = false;
};

struct HasEmptyElement : public Ope::Visitor {
  HasEmptyElement(STL::list<STL::pair<const char *, STL::string>> &refs)
      : refs_(refs) {}

  void visit(Sequence &ope) override {
    bool save_is_empty = false;
    const char *save_error_s = nullptr;
    STL::string save_error_name;
    for (auto op : ope.opes_) {
      op->accept(*this);
      if (!is_empty) { return; }
      save_is_empty = is_empty;
      save_error_s = error_s;
      save_error_name = error_name;
      is_empty = false;
      error_name.clear();
    }
    is_empty = save_is_empty;
    error_s = save_error_s;
    error_name = save_error_name;
  }
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
      if (is_empty) { return; }
    }
  }
  void visit(Repetition &ope) override {
    if (ope.min_ == 0) {
      set_error();
    } else {
      ope.ope_->accept(*this);
    }
  }
  void visit(AndPredicate &) override { set_error(); }
  void visit(NotPredicate &) override { set_error(); }
  void visit(LiteralString &ope) override {
    if (ope.lit_.empty()) { set_error(); }
  }
  void visit(CaptureScope &ope) override { ope.ope_->accept(*this); }
  void visit(Capture &ope) override { ope.ope_->accept(*this); }
  void visit(TokenBoundary &ope) override { ope.ope_->accept(*this); }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(WeakHolder &ope) override { ope.weak_.lock()->accept(*this); }
  void visit(Holder &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override { ope.ope_->accept(*this); }
  void visit(PrecedenceClimbing &ope) override { ope.atom_->accept(*this); }
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

  bool is_empty = false;
  const char *error_s = nullptr;
  STL::string error_name;

private:
  void set_error() {
    is_empty = true;
    error_s = refs_.back().first;
    error_name = refs_.back().second;
  }
  STL::list<STL::pair<const char *, STL::string>> &refs_;
};

struct DetectInfiniteLoop : public Ope::Visitor {
  DetectInfiniteLoop(const char *s, const STL::string &name) {
    refs_.emplace_back(s, name);
  }

  void visit(Sequence &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
      if (has_error) { return; }
    }
  }
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
      if (has_error) { return; }
    }
  }
  void visit(Repetition &ope) override {
    if (ope.max_ == STL::numeric_limits<size_t>::max()) {
      HasEmptyElement vis(refs_);
      ope.ope_->accept(vis);
      if (vis.is_empty) {
        has_error = true;
        error_s = vis.error_s;
        error_name = vis.error_name;
      }
    } else {
      ope.ope_->accept(*this);
    }
  }
  void visit(AndPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(NotPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(CaptureScope &ope) override { ope.ope_->accept(*this); }
  void visit(Capture &ope) override { ope.ope_->accept(*this); }
  void visit(TokenBoundary &ope) override { ope.ope_->accept(*this); }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(WeakHolder &ope) override { ope.weak_.lock()->accept(*this); }
  void visit(Holder &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override { ope.ope_->accept(*this); }
  void visit(PrecedenceClimbing &ope) override { ope.atom_->accept(*this); }
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

  bool has_error = false;
  const char *error_s = nullptr;
  STL::string error_name;

private:
  STL::list<STL::pair<const char *, STL::string>> refs_;
};

struct ReferenceChecker : public Ope::Visitor {
  ReferenceChecker(const Grammar &grammar,
                   const STL::vector<STL::string> &params)
      : grammar_(grammar), params_(params) {}

  void visit(Sequence &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(Repetition &ope) override { ope.ope_->accept(*this); }
  void visit(AndPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(NotPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(CaptureScope &ope) override { ope.ope_->accept(*this); }
  void visit(Capture &ope) override { ope.ope_->accept(*this); }
  void visit(TokenBoundary &ope) override { ope.ope_->accept(*this); }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(WeakHolder &ope) override { ope.weak_.lock()->accept(*this); }
  void visit(Holder &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override { ope.ope_->accept(*this); }
  void visit(PrecedenceClimbing &ope) override { ope.atom_->accept(*this); }
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

  STL::unordered_map<STL::string, const char *> error_s;
  STL::unordered_map<STL::string, STL::string> error_message;

private:
  const Grammar &grammar_;
  const STL::vector<STL::string> &params_;
};

struct LinkReferences : public Ope::Visitor {
  LinkReferences(Grammar &grammar, const STL::vector<STL::string> &params)
      : grammar_(grammar), params_(params) {}

  void visit(Sequence &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(PrioritizedChoice &ope) override {
    for (auto op : ope.opes_) {
      op->accept(*this);
    }
  }
  void visit(Repetition &ope) override { ope.ope_->accept(*this); }
  void visit(AndPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(NotPredicate &ope) override { ope.ope_->accept(*this); }
  void visit(CaptureScope &ope) override { ope.ope_->accept(*this); }
  void visit(Capture &ope) override { ope.ope_->accept(*this); }
  void visit(TokenBoundary &ope) override { ope.ope_->accept(*this); }
  void visit(Ignore &ope) override { ope.ope_->accept(*this); }
  void visit(WeakHolder &ope) override { ope.weak_.lock()->accept(*this); }
  void visit(Holder &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override { ope.ope_->accept(*this); }
  void visit(PrecedenceClimbing &ope) override { ope.atom_->accept(*this); }
  void visit(Recovery &ope) override { ope.ope_->accept(*this); }

private:
  Grammar &grammar_;
  const STL::vector<STL::string> &params_;
};

struct FindReference : public Ope::Visitor {
  FindReference(const STL::vector<STL::shared_ptr<Ope>> &args,
                const STL::vector<STL::string> &params)
      : args_(args), params_(params) {}

  void visit(Sequence &ope) override {
    STL::vector<STL::shared_ptr<Ope>> opes;
    for (auto o : ope.opes_) {
      o->accept(*this);
      opes.push_back(found_ope);
    }
    found_ope = STL::make_shared<Sequence>(opes);
  }
  void visit(PrioritizedChoice &ope) override {
    STL::vector<STL::shared_ptr<Ope>> opes;
    for (auto o : ope.opes_) {
      o->accept(*this);
      opes.push_back(found_ope);
    }
    found_ope = STL::make_shared<PrioritizedChoice>(opes);
  }
  void visit(Repetition &ope) override {
    ope.ope_->accept(*this);
    found_ope = rep(found_ope, ope.min_, ope.max_);
  }
  void visit(AndPredicate &ope) override {
    ope.ope_->accept(*this);
    found_ope = apd(found_ope);
  }
  void visit(NotPredicate &ope) override {
    ope.ope_->accept(*this);
    found_ope = npd(found_ope);
  }
  void visit(Dictionary &ope) override { found_ope = ope.shared_from_this(); }
  void visit(LiteralString &ope) override {
    found_ope = ope.shared_from_this();
  }
  void visit(CharacterClass &ope) override {
    found_ope = ope.shared_from_this();
  }
  void visit(Character &ope) override { found_ope = ope.shared_from_this(); }
  void visit(AnyCharacter &ope) override { found_ope = ope.shared_from_this(); }
  void visit(CaptureScope &ope) override {
    ope.ope_->accept(*this);
    found_ope = csc(found_ope);
  }
  void visit(Capture &ope) override {
    ope.ope_->accept(*this);
    found_ope = cap(found_ope, ope.match_action_);
  }
  void visit(TokenBoundary &ope) override {
    ope.ope_->accept(*this);
    found_ope = tok(found_ope);
  }
  void visit(Ignore &ope) override {
    ope.ope_->accept(*this);
    found_ope = ign(found_ope);
  }
  void visit(WeakHolder &ope) override { ope.weak_.lock()->accept(*this); }
  void visit(Holder &ope) override { ope.ope_->accept(*this); }
  void visit(Reference &ope) override;
  void visit(Whitespace &ope) override {
    ope.ope_->accept(*this);
    found_ope = wsp(found_ope);
  }
  void visit(PrecedenceClimbing &ope) override {
    ope.atom_->accept(*this);
    found_ope = csc(found_ope);
  }
  void visit(Recovery &ope) override {
    ope.ope_->accept(*this);
    found_ope = rec(found_ope);
  }

  STL::shared_ptr<Ope> found_ope;

private:
  const STL::vector<STL::shared_ptr<Ope>> &args_;
  const STL::vector<STL::string> &params_;
};

struct IsPrioritizedChoice : public Ope::Visitor {
  void visit(PrioritizedChoice &) override { result_ = true; }

  static bool check(Ope &ope) {
    IsPrioritizedChoice vis;
    ope.accept(vis);
    return vis.result_;
  }

private:
  bool result_ = false;
};

/*
 * Keywords
 */
static const char *WHITESPACE_DEFINITION_NAME = "%whitespace";
static const char *WORD_DEFINITION_NAME = "%word";
static const char *RECOVER_DEFINITION_NAME = "%recover";

/*
 * Definition
 */
class Definition {
public:
  struct Result {
    bool ret;
    bool recovered;
    size_t len;
    ErrorInfo error_info;
  };

  Definition() : holder_(STL::make_shared<Holder>(this)) {}

  Definition(const Definition &rhs) : name(rhs.name), holder_(rhs.holder_) {
    holder_->outer_ = this;
  }

  Definition(const STL::shared_ptr<Ope> &ope)
      : holder_(STL::make_shared<Holder>(this)) {
    *this <= ope;
  }

  operator STL::shared_ptr<Ope>() {
    return STL::make_shared<WeakHolder>(holder_);
  }

  Definition &operator<=(const STL::shared_ptr<Ope> &ope) {
    holder_->ope_ = ope;
    return *this;
  }

  Result parse(const char *s, size_t n, const char *path = nullptr,
               Log log = nullptr) const {
    SemanticValues vs;
    STL::any dt;
    return parse_core(s, n, vs, dt, path, log);
  }

  Result parse(const char *s, const char *path = nullptr,
               Log log = nullptr) const {
    size_t n = strlen(s);
    return parse(s, n, path, log);
  }

  Result parse(const char *s, size_t n, STL::any &dt,
               const char *path = nullptr, Log log = nullptr) const {
    SemanticValues vs;
    return parse_core(s, n, vs, dt, path, log);
  }

  Result parse(const char *s, STL::any &dt, const char *path = nullptr,
               Log log = nullptr) const {
    size_t n = strlen(s);
    return parse(s, n, dt, path, log);
  }

  template <typename T>
  Result parse_and_get_value(const char *s, size_t n, T &val,
                             const char *path = nullptr,
                             Log log = nullptr) const {
    SemanticValues vs;
    STL::any dt;
    Result r = parse_core(s, n, vs, dt, path, log);
    if (r.ret && !vs.empty() && vs.front().has_value()) {
      val = STL::any_cast<T>(vs[0]);
    }
    return r;
  }

  template <typename T>
  Result parse_and_get_value(const char *s, T &val, const char *path = nullptr,
                             Log log = nullptr) const {
    size_t n = strlen(s);
    return parse_and_get_value(s, n, val, path, log);
  }

  template <typename T>
  Result parse_and_get_value(const char *s, size_t n, STL::any &dt, T &val,
                             const char *path = nullptr,
                             Log log = nullptr) const {
    SemanticValues vs;
    Result r = parse_core(s, n, vs, dt, path, log);
    if (r.ret && !vs.empty() && vs.front().has_value()) {
      val = STL::any_cast<T>(vs[0]);
    }
    return r;
  }

  template <typename T>
  Result parse_and_get_value(const char *s, STL::any &dt, T &val,
                             const char *path = nullptr,
                             Log log = nullptr) const {
    size_t n = strlen(s);
    return parse_and_get_value(s, n, dt, val, path, log);
  }

  void operator=(Action a) { action = a; }

  template <typename T> Definition &operator,(T fn) {
    operator=(fn);
    return *this;
  }

  Definition &operator~() {
    ignoreSemanticValue = true;
    return *this;
  }

  void accept(Ope::Visitor &v) { holder_->accept(v); }

  STL::shared_ptr<Ope> get_core_operator() const { return holder_->ope_; }

  bool is_token() const {
    call_once(is_token_init_, [this]() {
      is_token_ = TokenChecker::is_token(*get_core_operator());
    });
    return is_token_;
  }

  STL::string name;
  const char *s_ = nullptr;

  size_t id = 0;
  Action action;
  STL::function<void(const char *s, size_t n, STL::any &dt)> enter;
  STL::function<void(const char *s, size_t n, size_t matchlen, STL::any &value,
                     STL::any &dt)>
      leave;
  bool ignoreSemanticValue = false;
  STL::shared_ptr<Ope> whitespaceOpe;
  STL::shared_ptr<Ope> wordOpe;
  bool enablePackratParsing = false;
  bool is_macro = false;
  STL::vector<STL::string> params;
  TracerEnter tracer_enter;
  TracerLeave tracer_leave;
  bool disable_action = false;

  STL::string error_message;

private:
  friend class Reference;
  friend class ParserGenerator;

  Definition &operator=(const Definition &rhs);
  Definition &operator=(Definition &&rhs);

  void initialize_definition_ids() const {
    call_once(definition_ids_init_, [&]() {
      AssignIDToDefinition vis;
      holder_->accept(vis);
      if (whitespaceOpe) { whitespaceOpe->accept(vis); }
      if (wordOpe) { wordOpe->accept(vis); }
      definition_ids_.swap(vis.ids);
    });
  }

  Result parse_core(const char *s, size_t n, SemanticValues &vs, STL::any &dt,
                    const char *path, Log log) const {
    initialize_definition_ids();

    STL::shared_ptr<Ope> ope = holder_;
    if (whitespaceOpe) { ope = STL::make_shared<Sequence>(whitespaceOpe, ope); }

    Context cxt(path, s, n, definition_ids_.size(), whitespaceOpe, wordOpe,
                enablePackratParsing, tracer_enter, tracer_leave, log);

    size_t len = ope->parse(s, n, vs, cxt, dt);
    return Result{success(len), cxt.recovered, len, cxt.error_info};
  }

  STL::shared_ptr<Holder> holder_;
  mutable OnceFlag is_token_init_;
  mutable bool is_token_ = false;
  mutable OnceFlag assign_id_to_definition_init_;
  mutable OnceFlag definition_ids_init_;
  mutable STL::unordered_map<void *, size_t> definition_ids_;
};

/*
 * Implementations
 */

inline size_t parse_literal(const char *s, size_t n, SemanticValues &vs,
                            Context &c, STL::any &dt, const STL::string &lit,
                            OnceFlag &init_is_word, bool &is_word,
                            bool ignore_case) {
  size_t i = 0;
  for (; i < lit.size(); i++) {
    if (i >= n || (ignore_case ? (std::tolower(s[i]) != std::tolower(lit[i]))
                               : (s[i] != lit[i]))) {
      c.set_error_pos(s, lit.c_str());
      return static_cast<size_t>(-1);
    }
  }

  // Word check
  SemanticValues dummy_vs;
  Context dummy_c(nullptr, c.s, c.l, 0, nullptr, nullptr, false, nullptr,
                  nullptr, nullptr);
  STL::any dummy_dt;

  call_once(init_is_word, [&]() {
    if (c.wordOpe) {
      size_t len =
          c.wordOpe->parse(lit.data(), lit.size(), dummy_vs, dummy_c, dummy_dt);
      is_word = success(len);
    }
  });

  if (is_word) {
    NotPredicate ope(c.wordOpe);
    size_t len = ope.parse(s + i, n - i, dummy_vs, dummy_c, dummy_dt);
    if (fail(len)) { return len; }
    i += len;
  }

  // Skip whiltespace
  if (!c.in_token_boundary_count) {
    if (c.whitespaceOpe) {
      size_t len = c.whitespaceOpe->parse(s + i, n - i, vs, c, dt);
      if (fail(len)) { return len; }
      i += len;
    }
  }

  return i;
}

inline void Context::set_error_pos(const char *a_s, const char *literal) {
  if (log) {
    if (error_info.error_pos <= a_s) {
      if (error_info.error_pos < a_s) {
        error_info.error_pos = a_s;
        error_info.expected_tokens.clear();
      }
      if (literal) {
        error_info.add(literal, true);
      } else if (!rule_stack.empty()) {
        auto rule = rule_stack.back();
        auto ope = rule->get_core_operator();
        auto token = FindLiteralToken::token(*ope);
        if (token && token[0] != '\0') {
          error_info.add(token, true);
        } else {
          error_info.add(rule->name.c_str(), false);
        }
      }
    }
  }
}

inline void Context::trace_enter(const Ope &ope, const char *a_s, size_t n,
                                 SemanticValues &vs, STL::any &dt) const {
  trace_ids.push_back(next_trace_id++);
  tracer_enter(ope, a_s, n, vs, *this, dt);
}

inline void Context::trace_leave(const Ope &ope, const char *a_s, size_t n,
                                 SemanticValues &vs, STL::any &dt,
                                 size_t len) const {
  tracer_leave(ope, a_s, n, vs, *this, dt, len);
  trace_ids.pop_back();
}

inline bool Context::is_traceable(const Ope &ope) const {
  if (tracer_enter && tracer_leave) {
    return !IsReference::check(const_cast<Ope &>(ope));
  }
  return false;
}

inline size_t Ope::parse(const char *s, size_t n, SemanticValues &vs,
                         Context &c, STL::any &dt) const {
  if (c.is_traceable(*this)) {
    c.trace_enter(*this, s, n, vs, dt);
    size_t len = parse_core(s, n, vs, c, dt);
    c.trace_leave(*this, s, n, vs, dt, len);
    return len;
  }
  return parse_core(s, n, vs, c, dt);
}

inline size_t Dictionary::parse_core(const char *s, size_t n,
                                     SemanticValues & /*vs*/, Context &c,
                                     STL::any & /*dt*/) const {
  size_t len = trie_.match(s, n);
  if (len > 0) { return len; }
  c.set_error_pos(s);
  return static_cast<size_t>(-1);
}

inline size_t LiteralString::parse_core(const char *s, size_t n,
                                        SemanticValues &vs, Context &c,
                                        STL::any &dt) const {
  return parse_literal(s, n, vs, c, dt, lit_, init_is_word_, is_word_,
                       ignore_case_);
}

inline size_t TokenBoundary::parse_core(const char *s, size_t n,
                                        SemanticValues &vs, Context &c,
                                        STL::any &dt) const {
  size_t len;
  {
    c.in_token_boundary_count++;
    auto se = make_scope_exit([&]() { c.in_token_boundary_count--; });
    len = ope_->parse(s, n, vs, c, dt);
  }

  if (success(len)) {
    vs.tokens.emplace_back(STL::string_view(s, len));

    if (!c.in_token_boundary_count) {
      if (c.whitespaceOpe) {
        size_t l = c.whitespaceOpe->parse(s + len, n - len, vs, c, dt);
        if (fail(l)) { return l; }
        len += l;
      }
    }
  }
  return len;
}

inline size_t Holder::parse_core(const char *s, size_t n, SemanticValues &vs,
                                 Context &c, STL::any &dt) const {
  if (!ope_) {
    throw std::logic_error("Uninitialized definition ope was used...");
  }

  // Macro reference
  if (outer_->is_macro) {
    c.rule_stack.push_back(outer_);
    size_t len = ope_->parse(s, n, vs, c, dt);
    c.rule_stack.pop_back();
    return len;
  }

  size_t len;
  STL::any val;

  c.packrat(s, outer_->id, len, val, [&](STL::any &a_val) {
    if (outer_->enter) { outer_->enter(s, n, dt); }

    auto se2 = make_scope_exit([&]() {
      c.pop();
      if (outer_->leave) { outer_->leave(s, n, len, a_val, dt); }
    });

    auto &chldsv = c.push();

    c.rule_stack.push_back(outer_);
    len = ope_->parse(s, n, chldsv, c, dt);
    c.rule_stack.pop_back();

    // Invoke action
    if (success(len)) {
      chldsv.sv_ = STL::string_view(s, len);
      chldsv.name_ = outer_->name;

      if (!IsPrioritizedChoice::check(*ope_)) {
        chldsv.choice_count_ = 0;
        chldsv.choice_ = 0;
      }

      try {
        a_val = reduce(chldsv, dt);
      } catch (const parse_error &e) {
        if (e.what()) {
          if (c.error_info.message_pos < s) {
            c.error_info.message_pos = s;
            c.error_info.message = e.what();
          }
        }
        len = static_cast<size_t>(-1);
      }
    }
  });

  if (success(len)) {
    if (!outer_->ignoreSemanticValue) {
      vs.emplace_back(STL::move(val));
      vs.tags.emplace_back(str2tag(outer_->name));
    }
  }

  return len;
}

inline STL::any Holder::reduce(SemanticValues &vs, STL::any &dt) const {
  if (outer_->action && !outer_->disable_action) {
    return outer_->action(vs, dt);
  } else if (vs.empty()) {
    return STL::any();
  } else {
    return STL::move(vs.front());
  }
}

inline const char *Holder::trace_name() const {
  if (trace_name_.empty()) { trace_name_ = "[" + outer_->name + "]"; }
  return trace_name_.data();
}

inline size_t Reference::parse_core(const char *s, size_t n, SemanticValues &vs,
                                    Context &c, STL::any &dt) const {
  if (rule_) {
    // Reference rule
    if (rule_->is_macro) {
      // Macro
      FindReference vis(c.top_args(), c.rule_stack.back()->params);

      // Collect arguments
      STL::vector<STL::shared_ptr<Ope>> args;
      for (auto arg : args_) {
        arg->accept(vis);
        args.emplace_back(STL::move(vis.found_ope));
      }

      c.push_args(STL::move(args));
      auto se = make_scope_exit([&]() { c.pop_args(); });
      auto ope = get_core_operator();
      return ope->parse(s, n, vs, c, dt);
    } else {
      // Definition
      c.push_args(STL::vector<STL::shared_ptr<Ope>>());
      auto se = make_scope_exit([&]() { c.pop_args(); });
      auto ope = get_core_operator();
      return ope->parse(s, n, vs, c, dt);
    }
  } else {
    // Reference parameter in macro
    const auto &args = c.top_args();
    return args[iarg_]->parse(s, n, vs, c, dt);
  }
}

inline STL::shared_ptr<Ope> Reference::get_core_operator() const {
  return rule_->holder_;
}

inline size_t BackReference::parse_core(const char *s, size_t n,
                                        SemanticValues &vs, Context &c,
                                        STL::any &dt) const {
  int size = static_cast<int>(c.capture_scope_stack_size);
  for (int i = size - 1; i >= 0; i--) {
    size_t index = static_cast<size_t>(i);
    const auto &cs = c.capture_scope_stack[index];
    if (cs.find(name_) != cs.end()) {
      const auto &lit = cs.at(name_);
      OnceFlag init_is_word;
      bool is_word = false;
      return parse_literal(s, n, vs, c, dt, lit, init_is_word, is_word, false);
    }
  }
  throw std::runtime_error("Invalid back reference...");
}

inline Definition &
PrecedenceClimbing::get_reference_for_binop(Context &c) const {
  if (rule_.is_macro) {
    // Reference parameter in macro
    const auto &args = c.top_args();
    size_t iarg = static_cast<Reference &>(*binop_).iarg_;
    STL::shared_ptr<Ope> arg = args[iarg];
    return *static_cast<Reference &>(*arg).rule_;
  }

  return *static_cast<Reference &>(*binop_).rule_;
}

inline size_t PrecedenceClimbing::parse_expression(const char *s, size_t n,
                                                   SemanticValues &vs,
                                                   Context &c, STL::any &dt,
                                                   size_t min_prec) const {
  size_t len = atom_->parse(s, n, vs, c, dt);
  if (fail(len)) { return len; }

  STL::string tok;
  auto &rule = get_reference_for_binop(c);
  auto action = STL::move(rule.action);

  rule.action = [&](SemanticValues &vs2, STL::any &dt2) {
    tok = vs2.token();
    if (action) {
      return action(vs2, dt2);
    } else if (!vs2.empty()) {
      return vs2[0];
    }
    return STL::any();
  };
  auto action_se = make_scope_exit([&]() { rule.action = STL::move(action); });

  size_t i = len;
  while (i < n) {
    STL::vector<STL::any> save_values(vs.begin(), vs.end());
    auto save_tokens = vs.tokens;

    auto chv = c.push();
    size_t chl = binop_->parse(s + i, n - i, chv, c, dt);
    c.pop();

    if (fail(chl)) { break; }

    auto it = info_.find(tok);
    if (it == info_.end()) { break; }

    auto level = STL::get<0>(it->second);
    auto assoc = STL::get<1>(it->second);

    if (level < min_prec) { break; }

    vs.emplace_back(STL::move(chv[0]));
    i += chl;

    auto next_min_prec = level;
    if (assoc == 'L') { next_min_prec = level + 1; }

    chv = c.push();
    chl = parse_expression(s + i, n - i, chv, c, dt, next_min_prec);
    c.pop();

    if (fail(chl)) {
      vs.assign(save_values.begin(), save_values.end());
      vs.tokens = save_tokens;
      break;
    }

    vs.emplace_back(STL::move(chv[0]));
    i += chl;

    STL::any val;
    if (rule_.action) {
      vs.sv_ = STL::string_view(s, i);
      val = rule_.action(vs, dt);
    } else if (!vs.empty()) {
      val = vs[0];
    }
    vs.clear();
    vs.emplace_back(STL::move(val));
  }

  return i;
}

inline size_t Recovery::parse_core(const char *s, size_t n, SemanticValues &/*vs*/,
                                   Context &c, STL::any &/*dt*/) const {
  auto save_log = c.log;
  c.log = nullptr;

  const Reference &rule = static_cast<Reference &>(*ope_);

  SemanticValues dummy_vs;
  STL::any dummy_dt;
  size_t len = rule.parse(s, n, dummy_vs, c, dummy_dt);

  c.log = save_log;

  if (success(len)) {
    c.recovered = true;
    if (c.log) {
      // auto label = dynamic_cast<Reference *>(rule.args_[0].get());
      // if (rule.args_[0].get())
      //   assert(label);
      // if (label) {
      //   if (!label->rule_->error_message.empty()) {
      //     c.error_info.message_pos = c.error_info.error_pos;
      //     c.error_info.message = label->rule_->error_message;
      //   }
      // }

      // No need for language-level RTTI
      STL::shared_ptr<Ope> ope = rule.args_[0];
      if (ope) {
        STL::string name = TraceOpeName::get(*ope);
        assert(name == "Reference");
        Reference *label = static_cast<Reference *>(ope.get());
        if (!label->rule_->error_message.empty()) {
          c.error_info.message_pos = c.error_info.error_pos;
          c.error_info.message = label->rule_->error_message;
        }
      }

      c.error_info.output_log(c.log, c.s, c.l);
    }
  }
  c.error_info.clear();

  return len;
}

inline void Sequence::accept(Visitor &v) { v.visit(*this); }
inline void PrioritizedChoice::accept(Visitor &v) { v.visit(*this); }
inline void Repetition::accept(Visitor &v) { v.visit(*this); }
inline void AndPredicate::accept(Visitor &v) { v.visit(*this); }
inline void NotPredicate::accept(Visitor &v) { v.visit(*this); }
inline void Dictionary::accept(Visitor &v) { v.visit(*this); }
inline void LiteralString::accept(Visitor &v) { v.visit(*this); }
inline void CharacterClass::accept(Visitor &v) { v.visit(*this); }
inline void Character::accept(Visitor &v) { v.visit(*this); }
inline void AnyCharacter::accept(Visitor &v) { v.visit(*this); }
inline void CaptureScope::accept(Visitor &v) { v.visit(*this); }
inline void Capture::accept(Visitor &v) { v.visit(*this); }
inline void TokenBoundary::accept(Visitor &v) { v.visit(*this); }
inline void Ignore::accept(Visitor &v) { v.visit(*this); }
inline void User::accept(Visitor &v) { v.visit(*this); }
inline void WeakHolder::accept(Visitor &v) { v.visit(*this); }
inline void Holder::accept(Visitor &v) { v.visit(*this); }
inline void Reference::accept(Visitor &v) { v.visit(*this); }
inline void Whitespace::accept(Visitor &v) { v.visit(*this); }
inline void BackReference::accept(Visitor &v) { v.visit(*this); }
inline void PrecedenceClimbing::accept(Visitor &v) { v.visit(*this); }
inline void Recovery::accept(Visitor &v) { v.visit(*this); }

inline void AssignIDToDefinition::visit(Holder &ope) {
  void* p = static_cast<void *>(ope.outer_);
  if (ids.count(p)) { return; }
  size_t id = ids.size();
  ids[p] = id;
  ope.outer_->id = id;
  ope.ope_->accept(*this);
}

inline void AssignIDToDefinition::visit(Reference &ope) {
  if (ope.rule_) {
    for (auto arg : ope.args_) {
      arg->accept(*this);
    }
    ope.rule_->accept(*this);
  }
}

inline void AssignIDToDefinition::visit(PrecedenceClimbing &ope) {
  ope.atom_->accept(*this);
  ope.binop_->accept(*this);
}

inline void TokenChecker::visit(Reference &ope) {
  if (ope.is_macro_) {
    for (auto arg : ope.args_) {
      arg->accept(*this);
    }
  } else {
    has_rule_ = true;
  }
}

inline void FindLiteralToken::visit(Reference &ope) {
  if (ope.is_macro_) {
    ope.rule_->accept(*this);
    for (auto arg : ope.args_) {
      arg->accept(*this);
    }
  }
}

inline void DetectLeftRecursion::visit(Reference &ope) {
  if (ope.name_ == name_) {
    error_s = ope.s_;
  } else if (!refs_.count(ope.name_)) {
    refs_.insert(ope.name_);
    if (ope.rule_) {
      ope.rule_->accept(*this);
      if (done_ == false) { return; }
    }
  }
  done_ = true;
}

inline void HasEmptyElement::visit(Reference &ope) {
  auto it = STL::find_if(refs_.begin(), refs_.end(),
                         [&](const STL::pair<const char *, STL::string> &ref) {
                           return ope.name_ == ref.second;
                         });
  if (it != refs_.end()) { return; }

  if (ope.rule_) {
    refs_.emplace_back(ope.s_, ope.name_);
    ope.rule_->accept(*this);
    refs_.pop_back();
  }
}

inline void DetectInfiniteLoop::visit(Reference &ope) {
  auto it = STL::find_if(refs_.begin(), refs_.end(),
                         [&](const STL::pair<const char *, STL::string> &ref) {
                           return ope.name_ == ref.second;
                         });
  if (it != refs_.end()) { return; }

  if (ope.rule_) {
    refs_.emplace_back(ope.s_, ope.name_);
    ope.rule_->accept(*this);
    refs_.pop_back();
  }
}

inline void ReferenceChecker::visit(Reference &ope) {
  auto it = STL::find(params_.begin(), params_.end(), ope.name_);
  if (it != params_.end()) { return; }

  if (!grammar_.count(ope.name_)) {
    error_s[ope.name_] = ope.s_;
    error_message[ope.name_] = "'" + ope.name_ + "' is not defined.";
  } else {
    const auto &rule = grammar_.at(ope.name_);
    if (rule.is_macro) {
      if (!ope.is_macro_ || ope.args_.size() != rule.params.size()) {
        error_s[ope.name_] = ope.s_;
        error_message[ope.name_] = "incorrect number of arguments.";
      }
    } else if (ope.is_macro_) {
      error_s[ope.name_] = ope.s_;
      error_message[ope.name_] = "'" + ope.name_ + "' is not macro.";
    }
    for (auto arg : ope.args_) {
      arg->accept(*this);
    }
  }
}

inline void LinkReferences::visit(Reference &ope) {
  // Check if the reference is a macro parameter
  bool found_param = false;
  for (size_t i = 0; i < params_.size(); i++) {
    const auto &param = params_[i];
    if (param == ope.name_) {
      ope.iarg_ = i;
      found_param = true;
      break;
    }
  }

  // Check if the reference is a definition rule
  if (!found_param && grammar_.count(ope.name_)) {
    auto &rule = grammar_.at(ope.name_);
    ope.rule_ = &rule;
  }

  for (auto arg : ope.args_) {
    arg->accept(*this);
  }
}

inline void FindReference::visit(Reference &ope) {
  for (size_t i = 0; i < args_.size(); i++) {
    const auto &name = params_[i];
    if (name == ope.name_) {
      found_ope = args_[i];
      return;
    }
  }
  found_ope = ope.shared_from_this();
}

/*-----------------------------------------------------------------------------
 *  PEG parser generator
 *---------------------------------------------------------------------------*/

using Rules = STL::unordered_map<STL::string, STL::shared_ptr<Ope>>;

class ParserGenerator {
public:
  static STL::shared_ptr<Grammar> parse(const char *s, size_t n,
                                        const Rules &rules, STL::string &start,
                                        Log log) {
    return get_instance().perform_core(s, n, rules, start, log);
  }

  static STL::shared_ptr<Grammar> parse(const char *s, size_t n,
                                        STL::string &start, Log log) {
    Rules dummy;
    return parse(s, n, dummy, start, log);
  }

  // For debuging purpose
  static Grammar &grammar() { return get_instance().g; }

private:
  static ParserGenerator &get_instance() {
    static ParserGenerator instance;
    return instance;
  }

  ParserGenerator() {
    make_grammar();
    setup_actions();
  }

  struct Instruction {
    STL::string type;
    STL::any data;
  };

  struct Data {
    STL::shared_ptr<Grammar> grammar;
    STL::string start;
    const char *start_pos = nullptr;
    STL::vector<STL::pair<STL::string, const char *>> duplicates;
    STL::map<STL::string, Instruction> instructions;

    Data() : grammar(STL::make_shared<Grammar>()) {}
  };

  void make_grammar() {
    // Setup PEG syntax parser
    g["Grammar"] <= seq(g["Spacing"], oom(g["Definition"]), g["EndOfFile"]);
    g["Definition"] <=
        cho(seq(g["Ignore"], g["IdentCont"], g["Parameters"], g["LEFTARROW"],
                g["Expression"], opt(g["Instruction"])),
            seq(g["Ignore"], g["Identifier"], g["LEFTARROW"], g["Expression"],
                opt(g["Instruction"])));
    g["Expression"] <= seq(g["Sequence"], zom(seq(g["SLASH"], g["Sequence"])));
    g["Sequence"] <= zom(g["Prefix"]);
    g["Prefix"] <= seq(opt(cho(g["AND"], g["NOT"])), g["SuffixWithLabel"]);
    g["SuffixWithLabel"] <=
        seq(g["Suffix"], opt(seq(g["HAT"], g["Identifier"])));
    g["Suffix"] <= seq(g["Primary"], opt(g["Loop"]));
    g["Loop"] <= cho(g["QUESTION"], g["STAR"], g["PLUS"], g["Repetition"]);
    g["Primary"] <=
        cho(seq(g["Ignore"], g["IdentCont"], g["Arguments"],
                npd(g["LEFTARROW"])),
            seq(g["Ignore"], g["Identifier"],
                npd(seq(opt(g["Parameters"]), g["LEFTARROW"]))),
            seq(g["OPEN"], g["Expression"], g["CLOSE"]),
            seq(g["BeginTok"], g["Expression"], g["EndTok"]),
            seq(g["BeginCapScope"], g["Expression"], g["EndCapScope"]),
            seq(g["BeginCap"], g["Expression"], g["EndCap"]), g["BackRef"],
            g["LiteralI"], g["Dictionary"], g["Literal"], g["NegatedClass"],
            g["Class"], g["DOT"]);

    g["Identifier"] <= seq(g["IdentCont"], g["Spacing"]);
    g["IdentCont"] <= seq(g["IdentStart"], zom(g["IdentRest"]));

    const static STL::vector<STL::pair<char32_t, char32_t>> range = {
        {0x0080, 0xFFFF}};
    g["IdentStart"] <= cho(cls("a-zA-Z_%"), cls(range));

    g["IdentRest"] <= cho(g["IdentStart"], cls("0-9"));

    g["Dictionary"] <= seq(g["LiteralD"], oom(seq(g["PIPE"], g["LiteralD"])));

    auto lit_ope = cho(seq(cls("'"), tok(zom(seq(npd(cls("'")), g["Char"]))),
                           cls("'"), g["Spacing"]),
                       seq(cls("\""), tok(zom(seq(npd(cls("\"")), g["Char"]))),
                           cls("\""), g["Spacing"]));
    g["Literal"] <= lit_ope;
    g["LiteralD"] <= lit_ope;

    g["LiteralI"] <=
        cho(seq(cls("'"), tok(zom(seq(npd(cls("'")), g["Char"]))), lit("'i"),
                g["Spacing"]),
            seq(cls("\""), tok(zom(seq(npd(cls("\"")), g["Char"]))), lit("\"i"),
                g["Spacing"]));

    // NOTE: The original Brian Ford's paper uses 'zom' instead of 'oom'.
    g["Class"] <= seq(chr('['), npd(chr('^')),
                      tok(oom(seq(npd(chr(']')), g["Range"]))), chr(']'),
                      g["Spacing"]);
    g["NegatedClass"] <= seq(lit("[^"),
                             tok(oom(seq(npd(chr(']')), g["Range"]))), chr(']'),
                             g["Spacing"]);

    g["Range"] <= cho(seq(g["Char"], chr('-'), g["Char"]), g["Char"]);
    g["Char"] <=
        cho(seq(chr('\\'), cls("nrt'\"[]\\^")),
            seq(chr('\\'), cls("0-3"), cls("0-7"), cls("0-7")),
            seq(chr('\\'), cls("0-7"), opt(cls("0-7"))),
            seq(lit("\\x"), cls("0-9a-fA-F"), opt(cls("0-9a-fA-F"))),
            seq(lit("\\u"),
                cho(seq(cho(seq(chr('0'), cls("0-9a-fA-F")), lit("10")),
                        rep(cls("0-9a-fA-F"), 4, 4)),
                    rep(cls("0-9a-fA-F"), 4, 5))),
            seq(npd(chr('\\')), dot()));

    g["Repetition"] <=
        seq(g["BeginBlacket"], g["RepetitionRange"], g["EndBlacket"]);
    g["RepetitionRange"] <= cho(seq(g["Number"], g["COMMA"], g["Number"]),
                                seq(g["Number"], g["COMMA"]), g["Number"],
                                seq(g["COMMA"], g["Number"]));
    g["Number"] <= seq(oom(cls("0-9")), g["Spacing"]);

    g["LEFTARROW"] <=
        seq(cho(lit("<-"), lit(reinterpret_cast<const char *>(u8"←"))),
            g["Spacing"]);
    ~g["SLASH"] <= seq(chr('/'), g["Spacing"]);
    ~g["PIPE"] <= seq(chr('|'), g["Spacing"]);
    g["AND"] <= seq(chr('&'), g["Spacing"]);
    g["NOT"] <= seq(chr('!'), g["Spacing"]);
    ~g["HAT"] <= seq(chr('^'), g["Spacing"]);
    g["QUESTION"] <= seq(chr('?'), g["Spacing"]);
    g["STAR"] <= seq(chr('*'), g["Spacing"]);
    g["PLUS"] <= seq(chr('+'), g["Spacing"]);
    ~g["OPEN"] <= seq(chr('('), g["Spacing"]);
    ~g["CLOSE"] <= seq(chr(')'), g["Spacing"]);
    g["DOT"] <= seq(chr('.'), g["Spacing"]);

    ~g["Spacing"] <= zom(cho(g["Space"], g["Comment"]));
    g["Comment"] <=
        seq(chr('#'), zom(seq(npd(g["EndOfLine"]), dot())), g["EndOfLine"]);
    g["Space"] <= cho(chr(' '), chr('\t'), g["EndOfLine"]);
    g["EndOfLine"] <= cho(lit("\r\n"), chr('\n'), chr('\r'));
    g["EndOfFile"] <= npd(dot());

    ~g["BeginTok"] <= seq(chr('<'), g["Spacing"]);
    ~g["EndTok"] <= seq(chr('>'), g["Spacing"]);

    ~g["BeginCapScope"] <= seq(chr('$'), chr('('), g["Spacing"]);
    ~g["EndCapScope"] <= seq(chr(')'), g["Spacing"]);

    g["BeginCap"] <= seq(chr('$'), tok(g["IdentCont"]), chr('<'), g["Spacing"]);
    ~g["EndCap"] <= seq(chr('>'), g["Spacing"]);

    g["BackRef"] <= seq(chr('$'), tok(g["IdentCont"]), g["Spacing"]);

    g["IGNORE"] <= chr('~');

    g["Ignore"] <= opt(g["IGNORE"]);
    g["Parameters"] <= seq(g["OPEN"], g["Identifier"],
                           zom(seq(g["COMMA"], g["Identifier"])), g["CLOSE"]);
    g["Arguments"] <= seq(g["OPEN"], g["Expression"],
                          zom(seq(g["COMMA"], g["Expression"])), g["CLOSE"]);
    ~g["COMMA"] <= seq(chr(','), g["Spacing"]);

    // Instruction grammars
    g["Instruction"] <=
        seq(g["BeginBlacket"],
            cho(cho(g["PrecedenceClimbing"]), cho(g["ErrorMessage"])),
            g["EndBlacket"]);

    ~g["SpacesZom"] <= zom(g["Space"]);
    ~g["SpacesOom"] <= oom(g["Space"]);
    ~g["BeginBlacket"] <= seq(chr('{'), g["Spacing"]);
    ~g["EndBlacket"] <= seq(chr('}'), g["Spacing"]);

    // PrecedenceClimbing instruction
    g["PrecedenceClimbing"] <=
        seq(lit("precedence"), g["SpacesOom"], g["PrecedenceInfo"],
            zom(seq(g["SpacesOom"], g["PrecedenceInfo"])), g["SpacesZom"]);
    g["PrecedenceInfo"] <=
        seq(g["PrecedenceAssoc"],
            oom(seq(ign(g["SpacesOom"]), g["PrecedenceOpe"])));
    g["PrecedenceOpe"] <=
        tok(oom(
            seq(npd(cho(g["PrecedenceAssoc"], g["Space"], chr('}'))), dot())));
    g["PrecedenceAssoc"] <= cls("LR");

    // Error message instruction
    g["ErrorMessage"] <=
        seq(lit("message"), g["SpacesOom"], g["LiteralD"], g["SpacesZom"]);

    // Set definition names
    for (auto &x : g) {
      x.second.name = x.first;
    }
  }

  void setup_actions() {
    g["Definition"] = Action([&](const SemanticValues &vs, STL::any &dt) {
      auto &data = *STL::any_cast<Data *>(dt);

      bool is_macro = vs.choice() == 0;
      bool ignore = STL::any_cast<bool>(vs[0]);
      const STL::string &name = STL::any_cast<STL::string>(vs[1]);

      STL::vector<STL::string> params;
      STL::shared_ptr<Ope> ope;
      if (is_macro) {
        params = STL::any_cast<STL::vector<STL::string>>(vs[2]);
        ope = STL::any_cast<STL::shared_ptr<Ope>>(vs[4]);
        if (vs.size() == 6) {
          data.instructions[name] = STL::any_cast<Instruction>(vs[5]);
        }
      } else {
        ope = STL::any_cast<STL::shared_ptr<Ope>>(vs[3]);
        if (vs.size() == 5) {
          data.instructions[name] = STL::any_cast<Instruction>(vs[4]);
        }
      }

      Grammar &grammar = *data.grammar;
      if (!grammar.count(name)) {
        auto &rule = grammar[name];
        rule <= ope;
        rule.name = name;
        rule.s_ = vs.sv().data();
        rule.ignoreSemanticValue = ignore;
        rule.is_macro = is_macro;
        rule.params = params;

        if (data.start.empty()) {
          data.start = name;
          data.start_pos = vs.sv().data();
        }
      } else {
        data.duplicates.emplace_back(name, vs.sv().data());
      }
      return STL::any();
    });

    g["Expression"] = Action([&](const SemanticValues &vs, STL::any &) {
      if (vs.size() == 1) {
        return STL::any_cast<STL::shared_ptr<Ope>>(vs[0]);
      } else {
        STL::vector<STL::shared_ptr<Ope>> opes;
        for (size_t i = 0u; i < vs.size(); i++) {
          opes.emplace_back(STL::any_cast<STL::shared_ptr<Ope>>(vs[i]));
        }
        const STL::shared_ptr<Ope> ope =
            STL::make_shared<PrioritizedChoice>(opes);
        return ope;
      }
    });

    g["Sequence"] = Action([&](const SemanticValues &vs, STL::any &) {
      if (vs.empty()) {
        return npd(lit(""));
      } else if (vs.size() == 1) {
        return STL::any_cast<STL::shared_ptr<Ope>>(vs[0]);
      } else {
        STL::vector<STL::shared_ptr<Ope>> opes;
        for (const auto &x : vs) {
          opes.emplace_back(STL::any_cast<STL::shared_ptr<Ope>>(x));
        }
        const STL::shared_ptr<Ope> ope = STL::make_shared<Sequence>(opes);
        return ope;
      }
    });

    g["Prefix"] = Action([&](const SemanticValues &vs, STL::any &) {
      STL::shared_ptr<Ope> ope;
      if (vs.size() == 1) {
        ope = STL::any_cast<STL::shared_ptr<Ope>>(vs[0]);
      } else {
        assert(vs.size() == 2);
        char tok = STL::any_cast<char>(vs[0]);
        ope = STL::any_cast<STL::shared_ptr<Ope>>(vs[1]);
        if (tok == '&') {
          ope = apd(ope);
        } else { // '!'
          ope = npd(ope);
        }
      }
      return ope;
    });

    g["SuffixWithLabel"] = Action([&](const SemanticValues &vs, STL::any &dt) {
      auto ope = STL::any_cast<STL::shared_ptr<Ope>>(vs[0]);
      if (vs.size() == 1) {
        return ope;
      } else {
        assert(vs.size() == 2);
        Data &data = *STL::any_cast<Data *>(dt);
        const STL::string &ident = STL::any_cast<STL::string>(vs[1]);
        auto label = ref(*data.grammar, ident, vs.sv().data(), false, {});
        auto recovery = rec(ref(*data.grammar, RECOVER_DEFINITION_NAME,
                                vs.sv().data(), true, {label}));
        return cho(ope, recovery);
      }
    });

    struct Loop {
      enum class Type { opt = 0, zom, oom, rep };
      Type type;
      STL::pair<size_t, size_t> range;
    };

    g["Suffix"] = Action([&](const SemanticValues &vs, STL::any &) {
      auto ope = STL::any_cast<STL::shared_ptr<Ope>>(vs[0]);
      if (vs.size() == 1) {
        return ope;
      } else {
        assert(vs.size() == 2);
        auto loop = STL::any_cast<Loop>(vs[1]);
        switch (loop.type) {
        case Loop::Type::opt: return opt(ope);
        case Loop::Type::zom: return zom(ope);
        case Loop::Type::oom: return oom(ope);
        default: // Regex-like repetition
          return rep(ope, loop.range.first, loop.range.second);
        }
      }
    });

    g["Loop"] = Action([&](const SemanticValues &vs, STL::any &) {
      switch (vs.choice()) {
      case 0: // Option
        return Loop{Loop::Type::opt, STL::pair<size_t, size_t>()};
      case 1: // Zero or More
        return Loop{Loop::Type::zom, STL::pair<size_t, size_t>()};
      case 2: // One or More
        return Loop{Loop::Type::oom, STL::pair<size_t, size_t>()};
      default: // Regex-like repetition
        return Loop{Loop::Type::rep,
                    STL::any_cast<STL::pair<size_t, size_t>>(vs[0])};
      }
    });

    g["RepetitionRange"] = Action([&](const SemanticValues &vs, STL::any) {
      switch (vs.choice()) {
      case 0: { // Number COMMA Number
        size_t min = STL::any_cast<size_t>(vs[0]);
        size_t max = STL::any_cast<size_t>(vs[1]);
        return STL::make_pair(min, max);
      }
      case 1: // Number COMMA
        return STL::make_pair(STL::any_cast<size_t>(vs[0]),
                         STL::numeric_limits<size_t>::max());
      case 2: { // Number
        size_t n = STL::any_cast<size_t>(vs[0]);
        return STL::make_pair(n, n);
      }
      default: // COMMA Number
        return STL::make_pair(STL::numeric_limits<size_t>::min(),
                         STL::any_cast<size_t>(vs[0]));
      }
    });
    //g["Number"] = [&](const SemanticValues &vs) {
    //  return vs.token_to_number<size_t>();
    //};

    g["Primary"] = Action([&](const SemanticValues &vs, STL::any &dt) {
      Data &data = *STL::any_cast<Data *>(dt);

      switch (vs.choice()) {
      case 0:   // Macro Reference
      case 1: { // Reference
        bool is_macro = vs.choice() == 0;
        bool ignore = STL::any_cast<bool>(vs[0]);
        const STL::string &ident = STL::any_cast<STL::string>(vs[1]);

        STL::vector<STL::shared_ptr<Ope>> args;
        if (is_macro) {
          args = STL::any_cast<STL::vector<STL::shared_ptr<Ope>>>(vs[2]);
        }

        auto ope = ref(*data.grammar, ident, vs.sv().data(), is_macro, args);
        if (ident == RECOVER_DEFINITION_NAME) { ope = rec(ope); }

        if (ignore) {
          return ign(ope);
        } else {
          return ope;
        }
      }
      case 2: { // (Expression)
        return STL::any_cast<STL::shared_ptr<Ope>>(vs[0]);
      }
      case 3: { // TokenBoundary
        return tok(STL::any_cast<STL::shared_ptr<Ope>>(vs[0]));
      }
      case 4: { // CaptureScope
        return csc(STL::any_cast<STL::shared_ptr<Ope>>(vs[0]));
      }
      case 5: { // Capture
        const STL::string_view &name = STL::any_cast<STL::string_view>(vs[0]);
        auto ope = STL::any_cast<STL::shared_ptr<Ope>>(vs[1]);
        return cap(ope, [name](const char *a_s, size_t a_n, Context &c) {
          auto &cs = c.capture_scope_stack[c.capture_scope_stack_size - 1];
          cs[name] = STL::string(a_s, a_n);
        });
      }
      default: {
        return STL::any_cast<STL::shared_ptr<Ope>>(vs[0]);
      }
      }
    });

    g["IdentCont"] = Action([](const SemanticValues &vs, STL::any &) {
      return STL::string(vs.sv().data(), vs.sv().length());
    });

    g["Dictionary"] = Action([](const SemanticValues &vs, STL::any &) {
      auto items = vs.transform<STL::string>();
      return dic(items);
    });

    g["Literal"] = Action([](const SemanticValues &vs, STL::any &) {
      const auto &tok = vs.tokens.front();
      return lit(resolve_escape_sequence(tok.data(), tok.size()));
    });
    g["LiteralI"] = Action([](const SemanticValues &vs, STL::any &) {
      const auto &tok = vs.tokens.front();
      return liti(resolve_escape_sequence(tok.data(), tok.size()));
    });
    g["LiteralD"] = Action([](const SemanticValues &vs, STL::any &) {
      auto &tok = vs.tokens.front();
      return resolve_escape_sequence(tok.data(), tok.size());
    });

    g["Class"] = Action([](const SemanticValues &vs, STL::any &) {
      auto ranges = vs.transform<STL::pair<char32_t, char32_t>>();
      return cls(ranges);
    });
    g["NegatedClass"] = Action([](const SemanticValues &vs, STL::any &) {
      auto ranges = vs.transform<STL::pair<char32_t, char32_t>>();
      return ncls(ranges);
    });
    g["Range"] = Action([](const SemanticValues &vs, STL::any &) {
      switch (vs.choice()) {
      case 0: {
        auto s1 = STL::any_cast<STL::string>(vs[0]);
        auto s2 = STL::any_cast<STL::string>(vs[1]);
        auto cp1 = decode_codepoint(s1.data(), s1.length());
        auto cp2 = decode_codepoint(s2.data(), s2.length());
        return STL::make_pair(cp1, cp2);
      }
      case 1: {
        auto s = STL::any_cast<STL::string>(vs[0]);
        auto cp = decode_codepoint(s.data(), s.length());
        return STL::make_pair(cp, cp);
      }
      }
      return STL::pair<char32_t, char32_t>(0, 0);
    });
    g["Char"] = Action([](const SemanticValues &vs, STL::any &) {
      return resolve_escape_sequence(vs.sv().data(), vs.sv().length());
    });

    g["AND"] = Action([](const SemanticValues &vs, STL::any &) { return *vs.sv().data(); });
    g["NOT"] = Action([](const SemanticValues &vs, STL::any &) { return *vs.sv().data(); });
    g["QUESTION"] = Action([](const SemanticValues &vs, STL::any &) { return *vs.sv().data(); });
    g["STAR"] = Action([](const SemanticValues &vs, STL::any &) { return *vs.sv().data(); });
    g["PLUS"] = Action([](const SemanticValues &vs, STL::any &) { return *vs.sv().data(); });

    g["DOT"] = Action([](const SemanticValues & /*vs*/, STL::any &) { return dot(); });

    g["BeginCap"] = Action([](const SemanticValues &vs, STL::any &) { return vs.token(); });

    g["BackRef"] = Action([&](const SemanticValues &vs, STL::any &) {
      return bkr(vs.token_to_string());
    });

    g["Ignore"] = Action([](const SemanticValues &vs, STL::any &) { return vs.size() > 0; });

    g["Parameters"] = Action([](const SemanticValues &vs, STL::any &) {
      return vs.transform<STL::string>();
    });

    g["Arguments"] = Action([](const SemanticValues &vs, STL::any &) {
      return vs.transform<STL::shared_ptr<Ope>>();
    });

    g["PrecedenceClimbing"] = Action([](const SemanticValues &vs, STL::any &) {
      PrecedenceClimbing::BinOpeInfo binOpeInfo;
      size_t level = 1;
      for (auto v : vs) {
        auto tokens = STL::any_cast<STL::vector<STL::string_view>>(v);
        auto assoc = tokens[0][0];
        for (size_t i = 1; i < tokens.size(); i++) {
          binOpeInfo[tokens[i]] = STL::make_pair(level, assoc);
        }
        level++;
      }
      Instruction instruction;
      instruction.type = "precedence";
      instruction.data = binOpeInfo;
      return instruction;
    });
    g["PrecedenceInfo"] = Action([](const SemanticValues &vs, STL::any &) {
      return vs.transform<STL::string_view>();
    });
    g["PrecedenceOpe"] = Action([](const SemanticValues &vs, STL::any &) { return vs.token(); });
    g["PrecedenceAssoc"] = Action([](const SemanticValues &vs, STL::any &) { return vs.token(); });

    g["ErrorMessage"] = Action([](const SemanticValues &vs, STL::any &) {
      Instruction instruction;
      instruction.type = "message";
      instruction.data = STL::any_cast<STL::string>(vs[0]);
      return instruction;
    });
  }

  bool apply_precedence_instruction(Definition &rule,
                                    const PrecedenceClimbing::BinOpeInfo &info,
                                    const char *s, Log log) {
    try {
      Sequence &seq = static_cast<Sequence &>(*rule.get_core_operator());
      STL::shared_ptr<Ope> atom = seq.opes_[0];
      Repetition &rep = static_cast<Repetition &>(*seq.opes_[1]);
      Sequence &seq1 = static_cast<Sequence &>(*rep.ope_);
      STL::shared_ptr<Ope> binop = seq1.opes_[0];
      STL::shared_ptr<Ope> atom1 = seq1.opes_[1];

      const STL::string &atom_name = static_cast<Reference &>(*atom).name_;
      const STL::string &binop_name = static_cast<Reference &>(*binop).name_;
      const STL::string &atom1_name = static_cast<Reference &>(*atom1).name_;

      if (!rep.is_zom() || atom_name != atom1_name || atom_name == binop_name) {
        if (log) {
          auto line = line_info(s, rule.s_);
          log(line.first, line.second,
              "'precedence' instruction cannot be applied to '" + rule.name +
                  "'.");
        }
        return false;
      }

      rule.holder_->ope_ = pre(atom, binop, info, rule);
      rule.disable_action = true;
    } catch (...) {
      if (log) {
        auto line = line_info(s, rule.s_);
        log(line.first, line.second,
            "'precedence' instruction cannot be applied to '" + rule.name +
                "'.");
      }
      return false;
    }
    return true;
  }

  STL::shared_ptr<Grammar> perform_core(const char *s, size_t n,
                                        const Rules &rules, STL::string &start,
                                        Log log) {
    Data data;
    Grammar &grammar = *data.grammar;

    // Built-in macros
    {
      // `%recover`
      {
        Definition &rule = grammar[RECOVER_DEFINITION_NAME];
        rule <= ref(grammar, "x", "", false, {});
        rule.name = RECOVER_DEFINITION_NAME;
        rule.s_ = "[native]";
        rule.ignoreSemanticValue = true;
        rule.is_macro = true;
        rule.params = {"x"};
      }
    }

    STL::any dt = &data;
    Definition::Result r = g["Grammar"].parse(s, n, dt, nullptr, log);

    if (!r.ret) {
      if (log) {
        if (r.error_info.message_pos) {
          auto line = line_info(s, r.error_info.message_pos);
          log(line.first, line.second, r.error_info.message);
        } else {
          auto line = line_info(s, r.error_info.error_pos);
          log(line.first, line.second, "syntax error");
        }
      }
      return nullptr;
    }

    // User provided rules
    for (const auto &x : rules) {
      auto name = x.first;
      bool ignore = false;
      if (!name.empty() && name[0] == '~') {
        ignore = true;
        name.erase(0, 1);
      }
      if (!name.empty()) {
        auto &rule = grammar[name];
        rule <= x.second;
        rule.name = name;
        rule.ignoreSemanticValue = ignore;
      }
    }

    // Check duplicated definitions
    auto ret = data.duplicates.empty();

    for (const auto &x : data.duplicates) {
      if (log) {
        const auto &name = x.first;
        auto ptr = x.second;
        auto line = line_info(s, ptr);
        log(line.first, line.second, "'" + name + "' is already defined.");
      }
    }

    // Check if the start rule has ignore operator
    {
      Definition &rule = grammar[data.start];
      if (rule.ignoreSemanticValue) {
        if (log) {
          auto line = line_info(s, rule.s_);
          log(line.first, line.second,
              "Ignore operator cannot be applied to '" + rule.name + "'.");
        }
        ret = false;
      }
    }

    if (!ret) { return nullptr; }

    // Check missing definitions
    for (auto &x : grammar) {
      auto &rule = x.second;

      ReferenceChecker vis(grammar, rule.params);
      rule.accept(vis);
      for (const auto &y : vis.error_s) {
        const auto &name = y.first;
        const auto ptr = y.second;
        if (log) {
          auto line = line_info(s, ptr);
          log(line.first, line.second, vis.error_message[name]);
        }
        ret = false;
      }
    }

    if (!ret) { return nullptr; }

    // Link references
    for (auto &x : grammar) {
      auto &rule = x.second;
      LinkReferences vis(grammar, rule.params);
      rule.accept(vis);
    }

    // Check left recursion
    ret = true;

    for (auto &x : grammar) {
      const auto &name = x.first;
      auto &rule = x.second;

      DetectLeftRecursion vis(name);
      rule.accept(vis);
      if (vis.error_s) {
        if (log) {
          auto line = line_info(s, vis.error_s);
          log(line.first, line.second, "'" + name + "' is left recursive.");
        }
        ret = false;
      }
    }

    if (!ret) { return nullptr; }

    // Set root definition
    Definition &start_rule = grammar[data.start];


    for (STL::unordered_map<STL::string, Definition>::iterator it = grammar.begin(); it!=grammar.end(); ++it) {
      const STL::string &name = it->first;
      Definition &rule = it->second;
      DetectInfiniteLoop vis(rule.s_, name);
      rule.accept(vis);
      if (vis.has_error) {
        if (log) {
          auto line = line_info(s, vis.error_s);
          log(line.first, line.second,
              "infinite loop is detected in '" + vis.error_name + "'.");
        }
        return nullptr;
      }
    }

    // Automatic whitespace skipping
    if (grammar.count(WHITESPACE_DEFINITION_NAME)) {
      for (auto &x : grammar) {
        auto &rule = x.second;
        auto ope = rule.get_core_operator();
        if (IsLiteralToken::check(*ope)) { rule <= tok(ope); }
      }

      start_rule.whitespaceOpe =
          wsp(grammar[WHITESPACE_DEFINITION_NAME].get_core_operator());
    }

    // Word expression
    if (grammar.count(WORD_DEFINITION_NAME)) {
      start_rule.wordOpe = grammar[WORD_DEFINITION_NAME].get_core_operator();
    }

    // Apply instructions
    for (const auto &item : data.instructions) {
      const auto &name = item.first;
      const auto &instruction = item.second;
      auto &rule = grammar[name];

      if (instruction.type == "precedence") {
        const auto &info =
            STL::any_cast<PrecedenceClimbing::BinOpeInfo>(instruction.data);

        if (!apply_precedence_instruction(rule, info, s, log)) {
          return nullptr;
        }
      } else if (instruction.type == "message") {
        rule.error_message = STL::any_cast<STL::string>(instruction.data);
      }
    }

    // Set root definition
    start = data.start;

    return data.grammar;
  }

  Grammar g;
};

/*-----------------------------------------------------------------------------
 *  AST
 *---------------------------------------------------------------------------*/

template <typename Annotation> struct AstBase : public Annotation {
  AstBase(const char *path, size_t line, size_t column, const char *name,
          const STL::vector<STL::shared_ptr<AstBase>> &nodes,
          size_t position = 0, size_t length = 0, size_t choice_count = 0,
          size_t choice = 0)
      : path(path ? path : ""), line(line), column(column), name(name),
        position(position), length(length), choice_count(choice_count),
        choice(choice), original_name(name),
        original_choice_count(choice_count), original_choice(choice),
        tag(str2tag(name)), original_tag(tag), is_token(false), nodes(nodes) {}

  AstBase(const char *path, size_t line, size_t column, const char *name,
          const STL::string_view &token, size_t position = 0, size_t length = 0,
          size_t choice_count = 0, size_t choice = 0)
      : path(path ? path : ""), line(line), column(column), name(name),
        position(position), length(length), choice_count(choice_count),
        choice(choice), original_name(name),
        original_choice_count(choice_count), original_choice(choice),
        tag(str2tag(name)), original_tag(tag), is_token(true), token(token) {}

  AstBase(const AstBase &ast, const char *original_name, size_t position = 0,
          size_t length = 0, size_t original_choice_count = 0,
          size_t original_choise = 0)
      : path(ast.path), line(ast.line), column(ast.column), name(ast.name),
        position(position), length(length), choice_count(ast.choice_count),
        choice(ast.choice), original_name(original_name),
        original_choice_count(original_choice_count),
        original_choice(original_choise), tag(ast.tag),
        original_tag(str2tag(original_name)), is_token(ast.is_token),
        token(ast.token), nodes(ast.nodes), parent(ast.parent) {}

  const STL::string path;
  const size_t line = 1;
  const size_t column = 1;

  const STL::string name;
  size_t position;
  size_t length;
  const size_t choice_count;
  const size_t choice;
  const STL::string original_name;
  const size_t original_choice_count;
  const size_t original_choice;
  const unsigned int tag;
  const unsigned int original_tag;

  const bool is_token;
  const STL::string_view token;

  STL::vector<STL::shared_ptr<AstBase<Annotation>>> nodes;
  STL::weak_ptr<AstBase<Annotation>> parent;

  STL::string token_to_string() const {
    assert(is_token);
    return STL::string(token);
  }

  template <typename T> T token_to_number() const {
    assert(is_token);
    T n = 0;
    STL::from_chars(token.data(), token.data() + token.size(), n);
    return n;
  }
};

template <typename T>
void ast_to_s_core(const STL::shared_ptr<T> &ptr, STL::string &s, int level,
                   STL::function<STL::string(const T &ast, int level)> fn) {
  const auto &ast = *ptr;
  for (auto i = 0; i < level; i++) {
    s += "  ";
  }
  auto name = ast.original_name;
  if (ast.original_choice_count > 0) {
    name += "/" + STL::to_string(ast.original_choice);
  }
  if (ast.name != ast.original_name) { name += "[" + ast.name + "]"; }
  if (ast.is_token) {
    s += "- " + name + " (";
    s += STL::string(ast.token);
    s += ")\n";
  } else {
    s += "+ " + name + "\n";
  }
  if (fn) { s += fn(ast, level + 1); }
  for (auto node : ast.nodes) {
    ast_to_s_core(node, s, level + 1, fn);
  }
}

template <typename T>
STL::string
ast_to_s(const STL::shared_ptr<T> &ptr,
         STL::function<STL::string(const T &ast, int level)> fn = nullptr) {
  STL::string s;
  ast_to_s_core(ptr, s, 0, fn);
  return s;
}

struct AstOptimizer {
  AstOptimizer(bool mode, const STL::vector<STL::string> &rules = {})
      : mode_(mode), rules_(rules) {}

  template <typename T>
  STL::shared_ptr<T> optimize(STL::shared_ptr<T> original,
                              STL::shared_ptr<T> parent = nullptr) {
    bool found =
        STL::find(rules_.begin(), rules_.end(), original->name) != rules_.end();
    bool opt = mode_ ? !found : found;

    if (opt && original->nodes.size() == 1) {
      auto child = optimize(original->nodes[0], parent);
      return STL::make_shared<T>(*child, original->name.data(),
                                 original->choice_count, original->position,
                                 original->length, original->choice);
    }

    auto ast = STL::make_shared<T>(*original);
    ast->parent = parent;
    ast->nodes.clear();
    for (auto node : original->nodes) {
      auto child = optimize(node, ast);
      ast->nodes.push_back(child);
    }
    return ast;
  }

private:
  const bool mode_;
  const STL::vector<STL::string> rules_;
};

struct EmptyType {};
using Ast = AstBase<EmptyType>;

template <typename T = Ast> void add_ast_action(Definition &rule) {
  rule.action = [&](SemanticValues &vs, STL::any &) -> STL::any {
    auto line = vs.line_info();

    if (rule.is_token()) {
      return STL::any(STL::make_shared<T>(
          vs.path, line.first, line.second, rule.name.data(), vs.token(),
          STL::distance(vs.ss, vs.sv().data()), vs.sv().length(),
          vs.choice_count(), vs.choice()));
    }

    auto ast =
        STL::make_shared<T>(vs.path, line.first, line.second, rule.name.data(),
                            vs.transform<STL::shared_ptr<T>>(),
                            STL::distance(vs.ss, vs.sv().data()),
                            vs.sv().length(), vs.choice_count(), vs.choice());

    for (auto node : ast->nodes) {
      node->parent = ast;
    }
    return STL::any(ast);
  };
}

#define PEG_EXPAND(...) __VA_ARGS__
#define PEG_CONCAT(a, b) a##b
#define PEG_CONCAT2(a, b) PEG_CONCAT(a, b)

#define PEG_PICK(                                                              \
    a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, \
    a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, \
    a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, \
    a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, \
    a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, \
    a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, \
    a92, a93, a94, a95, a96, a97, a98, a99, a100, ...)                         \
  a100

#define PEG_COUNT(...)                                                         \
  PEG_EXPAND(PEG_PICK(                                                         \
      __VA_ARGS__, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87,    \
      86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69,  \
      68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51,  \
      50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33,  \
      32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15,  \
      14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0))

#define PEG_DEF_1(r)                                                           \
  peg::Definition r;                                                           \
  r.name = #r;                                                                 \
  peg::add_ast_action(r);

#define PEG_DEF_2(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_1(__VA_ARGS__))
#define PEG_DEF_3(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_2(__VA_ARGS__))
#define PEG_DEF_4(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_3(__VA_ARGS__))
#define PEG_DEF_5(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_4(__VA_ARGS__))
#define PEG_DEF_6(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_5(__VA_ARGS__))
#define PEG_DEF_7(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_6(__VA_ARGS__))
#define PEG_DEF_8(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_7(__VA_ARGS__))
#define PEG_DEF_9(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_8(__VA_ARGS__))
#define PEG_DEF_10(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_9(__VA_ARGS__))
#define PEG_DEF_11(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_10(__VA_ARGS__))
#define PEG_DEF_12(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_11(__VA_ARGS__))
#define PEG_DEF_13(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_12(__VA_ARGS__))
#define PEG_DEF_14(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_13(__VA_ARGS__))
#define PEG_DEF_15(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_14(__VA_ARGS__))
#define PEG_DEF_16(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_15(__VA_ARGS__))
#define PEG_DEF_17(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_16(__VA_ARGS__))
#define PEG_DEF_18(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_17(__VA_ARGS__))
#define PEG_DEF_19(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_18(__VA_ARGS__))
#define PEG_DEF_20(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_19(__VA_ARGS__))
#define PEG_DEF_21(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_20(__VA_ARGS__))
#define PEG_DEF_22(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_21(__VA_ARGS__))
#define PEG_DEF_23(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_22(__VA_ARGS__))
#define PEG_DEF_24(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_23(__VA_ARGS__))
#define PEG_DEF_25(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_24(__VA_ARGS__))
#define PEG_DEF_26(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_25(__VA_ARGS__))
#define PEG_DEF_27(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_26(__VA_ARGS__))
#define PEG_DEF_28(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_27(__VA_ARGS__))
#define PEG_DEF_29(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_28(__VA_ARGS__))
#define PEG_DEF_30(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_29(__VA_ARGS__))
#define PEG_DEF_31(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_30(__VA_ARGS__))
#define PEG_DEF_32(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_31(__VA_ARGS__))
#define PEG_DEF_33(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_32(__VA_ARGS__))
#define PEG_DEF_34(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_33(__VA_ARGS__))
#define PEG_DEF_35(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_34(__VA_ARGS__))
#define PEG_DEF_36(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_35(__VA_ARGS__))
#define PEG_DEF_37(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_36(__VA_ARGS__))
#define PEG_DEF_38(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_37(__VA_ARGS__))
#define PEG_DEF_39(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_38(__VA_ARGS__))
#define PEG_DEF_40(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_39(__VA_ARGS__))
#define PEG_DEF_41(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_40(__VA_ARGS__))
#define PEG_DEF_42(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_41(__VA_ARGS__))
#define PEG_DEF_43(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_42(__VA_ARGS__))
#define PEG_DEF_44(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_43(__VA_ARGS__))
#define PEG_DEF_45(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_44(__VA_ARGS__))
#define PEG_DEF_46(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_45(__VA_ARGS__))
#define PEG_DEF_47(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_46(__VA_ARGS__))
#define PEG_DEF_48(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_47(__VA_ARGS__))
#define PEG_DEF_49(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_48(__VA_ARGS__))
#define PEG_DEF_50(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_49(__VA_ARGS__))
#define PEG_DEF_51(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_50(__VA_ARGS__))
#define PEG_DEF_52(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_51(__VA_ARGS__))
#define PEG_DEF_53(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_52(__VA_ARGS__))
#define PEG_DEF_54(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_53(__VA_ARGS__))
#define PEG_DEF_55(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_54(__VA_ARGS__))
#define PEG_DEF_56(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_55(__VA_ARGS__))
#define PEG_DEF_57(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_56(__VA_ARGS__))
#define PEG_DEF_58(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_57(__VA_ARGS__))
#define PEG_DEF_59(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_58(__VA_ARGS__))
#define PEG_DEF_60(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_59(__VA_ARGS__))
#define PEG_DEF_61(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_60(__VA_ARGS__))
#define PEG_DEF_62(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_61(__VA_ARGS__))
#define PEG_DEF_63(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_62(__VA_ARGS__))
#define PEG_DEF_64(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_63(__VA_ARGS__))
#define PEG_DEF_65(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_64(__VA_ARGS__))
#define PEG_DEF_66(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_65(__VA_ARGS__))
#define PEG_DEF_67(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_66(__VA_ARGS__))
#define PEG_DEF_68(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_67(__VA_ARGS__))
#define PEG_DEF_69(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_68(__VA_ARGS__))
#define PEG_DEF_70(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_69(__VA_ARGS__))
#define PEG_DEF_71(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_70(__VA_ARGS__))
#define PEG_DEF_72(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_71(__VA_ARGS__))
#define PEG_DEF_73(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_72(__VA_ARGS__))
#define PEG_DEF_74(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_73(__VA_ARGS__))
#define PEG_DEF_75(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_74(__VA_ARGS__))
#define PEG_DEF_76(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_75(__VA_ARGS__))
#define PEG_DEF_77(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_76(__VA_ARGS__))
#define PEG_DEF_78(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_77(__VA_ARGS__))
#define PEG_DEF_79(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_78(__VA_ARGS__))
#define PEG_DEF_80(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_79(__VA_ARGS__))
#define PEG_DEF_81(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_80(__VA_ARGS__))
#define PEG_DEF_82(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_81(__VA_ARGS__))
#define PEG_DEF_83(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_82(__VA_ARGS__))
#define PEG_DEF_84(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_83(__VA_ARGS__))
#define PEG_DEF_85(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_84(__VA_ARGS__))
#define PEG_DEF_86(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_85(__VA_ARGS__))
#define PEG_DEF_87(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_86(__VA_ARGS__))
#define PEG_DEF_88(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_87(__VA_ARGS__))
#define PEG_DEF_89(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_88(__VA_ARGS__))
#define PEG_DEF_90(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_89(__VA_ARGS__))
#define PEG_DEF_91(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_90(__VA_ARGS__))
#define PEG_DEF_92(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_91(__VA_ARGS__))
#define PEG_DEF_93(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_92(__VA_ARGS__))
#define PEG_DEF_94(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_93(__VA_ARGS__))
#define PEG_DEF_95(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_94(__VA_ARGS__))
#define PEG_DEF_96(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_95(__VA_ARGS__))
#define PEG_DEF_97(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_96(__VA_ARGS__))
#define PEG_DEF_98(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_97(__VA_ARGS__))
#define PEG_DEF_99(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_98(__VA_ARGS__))
#define PEG_DEF_100(r1, ...) PEG_EXPAND(PEG_DEF_1(r1) PEG_DEF_99(__VA_ARGS__))

#define AST_DEFINITIONS(...)                                                   \
  PEG_EXPAND(PEG_CONCAT2(PEG_DEF_, PEG_COUNT(__VA_ARGS__))(__VA_ARGS__))

/*-----------------------------------------------------------------------------
 *  parser
 *---------------------------------------------------------------------------*/

class parser {
public:
  parser() = default;

  parser(const char *s, size_t n, const Rules &rules) {
    load_grammar(s, n, rules);
  }

  parser(const char *s, const Rules &rules) : parser(s, strlen(s), rules) {}

  parser(const char *s, size_t n) : parser(s, n, Rules()) {}

  parser(const char *s) : parser(s, strlen(s), Rules()) {}

  operator bool() { return grammar_ != nullptr; }

  bool load_grammar(const char *s, size_t n, const Rules &rules) {
    grammar_ = ParserGenerator::parse(s, n, rules, start_, log);
    return grammar_ != nullptr;
  }

  bool load_grammar(const char *s, size_t n) {
    return load_grammar(s, n, Rules());
  }

  bool load_grammar(const char *s, const Rules &rules) {
    size_t n = strlen(s);
    return load_grammar(s, n, rules);
  }

  bool load_grammar(const char *s) {
    size_t n = strlen(s);
    return load_grammar(s, n);
  }

  bool parse_n(const char *s, size_t n, const char *path = nullptr) const {
    if (grammar_ != nullptr) {
      const auto &rule = (*grammar_)[start_];
      return post_process(s, n, rule.parse(s, n, path, log));
    }
    return false;
  }

  bool parse(const char *s, const char *path = nullptr) const {
    size_t n = strlen(s);
    return parse_n(s, n, path);
  }

  bool parse_n(const char *s, size_t n, STL::any &dt,
               const char *path = nullptr) const {
    if (grammar_ != nullptr) {
      const auto &rule = (*grammar_)[start_];
      return post_process(s, n, rule.parse(s, n, dt, path, log));
    }
    return false;
  }

  bool parse(const char *s, STL::any &dt, const char *path = nullptr) const {
    size_t n = strlen(s);
    return parse_n(s, n, dt, path);
  }

  template <typename T>
  bool parse_n(const char *s, size_t n, T &val,
               const char *path = nullptr) const {
    if (grammar_ != nullptr) {
      const auto &rule = (*grammar_)[start_];
      return post_process(s, n, rule.parse_and_get_value(s, n, val, path, log));
    }
    return false;
  }

  template <typename T>
  bool parse(const char *s, T &val, const char *path = nullptr) const {
    size_t n = strlen(s);
    return parse_n(s, n, val, path);
  }

  template <typename T>
  bool parse_n(const char *s, size_t n, STL::any &dt, T &val,
               const char *path = nullptr) const {
    if (grammar_ != nullptr) {
      const auto &rule = (*grammar_)[start_];
      return post_process(s, n,
                          rule.parse_and_get_value(s, n, dt, val, path, log));
    }
    return false;
  }

  template <typename T>
  bool parse(const char *s, STL::any &dt, T &val,
             const char *path = nullptr) const {
    size_t n = strlen(s);
    return parse_n(s, n, dt, val, path);
  }

  Definition &operator[](const char *s) { return (*grammar_)[s]; }

  const Definition &operator[](const char *s) const { return (*grammar_)[s]; }

  STL::vector<STL::string> get_rule_names() {
    STL::vector<STL::string> rules;
    rules.reserve(grammar_->size());
    for (auto const &r : *grammar_) {
      rules.emplace_back(r.first);
    }
    return rules;
  }

  void enable_packrat_parsing() {
    if (grammar_ != nullptr) {
      auto &rule = (*grammar_)[start_];
      rule.enablePackratParsing = true;
    }
  }

  template <typename T = Ast> parser &enable_ast() {
    for (auto &x : *grammar_) {
      auto &rule = x.second;
      if (!rule.action) { add_ast_action<T>(rule); }
    }
    return *this;
  }

  void enable_trace(TracerEnter tracer_enter, TracerLeave tracer_leave) {
    if (grammar_ != nullptr) {
      auto &rule = (*grammar_)[start_];
      rule.tracer_enter = tracer_enter;
      rule.tracer_leave = tracer_leave;
    }
  }

  Log log;

private:
  bool post_process(const char *s, size_t n,
                    const Definition::Result &r) const {
    bool ret = r.ret && r.len == n;
    if (log && !ret) { r.error_info.output_log(log, s, n); }
    return ret && !r.recovered;
  }

  STL::shared_ptr<Grammar> grammar_;
  STL::string start_;
};

} // namespace peg
