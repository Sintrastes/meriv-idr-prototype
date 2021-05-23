
module Meriv.Core.Queries

||| A query in the schema s with result type r.
data Query (s : MvBaseSchema) r where
  -- Given a relation, and some constraints on the arguments
  -- based on mode...
  -- MkQuery :