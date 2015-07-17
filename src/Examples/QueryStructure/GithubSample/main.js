var github = require('octonode');
var fs = require('fs');
var client = github.client({
  username: 'username',
  password: 'password'
});

var repositories = []
var commits = []
var chosen = {}

var ROWS_NEEDED = 10000

var save = function() {
  s_repositories = JSON.stringify(repositories, null, 2)
  s_commits = JSON.stringify(commits, null, 2)
  console.log(s_repositories)
  console.log(s_commits)
  fs.writeFile('./repositories.json', s_repositories);
  fs.writeFile('./commits.json', s_commits);
}

var collect = function() {
  if (repositories.length + commits.length > ROWS_NEEDED) {
    save();
    return;
  }
  console.log(repositories.length + commits.length)
  repo_number = Math.floor(Math.random()*30000000);
  if (repo_number in chosen) {
    collect();
    return;
  }
  chosen[repo_number] = true
  client.get('/repositories', {since: repo_number}, function (err, status, body, headers) {
    var project_name = body[0]['full_name'];
    client.get('/repos/' + project_name, {}, function (err, status, body, headers) {
      try {
        var star = body['stargazers_count'];
        repositories.push({'project_name': project_name, 'star': star});
        client.get('/repos/' + project_name + '/commits', {}, function (err, status, body, headers) {
          for (i in body) {
            try {
              var hash = body[i]['sha'];
              var date = body[i]['commit']['committer']['date'];
              var timestamp = new Date(date).getTime();
              commits.push({'project_name': project_name, 'hash': hash, 'date': timestamp});
            } catch(err) {
            }
          }
          collect();
        });
      } catch(err) {
        collect()
      }
    });
  });
};

collect();
collect();
collect();
collect();
collect();
